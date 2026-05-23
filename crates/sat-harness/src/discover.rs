//! Benchmark discovery and expectation-manifest loading.

use std::cmp::Reverse;
use std::collections::{BTreeMap, HashSet};
use std::fs::{self, File};
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use bzip2::read::BzDecoder;
use flate2::read::MultiGzDecoder;
use walkdir::WalkDir;

use crate::model::{
    CaseRecord, DiscoveredCase, ExpectationRule, ExpectedQueryResult, QueryAnswer,
};

/// The hidden manifest file used to attach expected results to benchmark paths.
const EXPECTATIONS_FILE: &str = "expectations.tsv";

/// One metadata summary extracted from one SMT-LIB trace.
#[derive(Debug, Default)]
struct TraceMetadata {
    /// Declared SMT logic, when any.
    logic: Option<Box<str>>,
    /// Expected results attached to `check-sat` commands.
    expected_queries: Vec<ExpectedQueryResult>,
}

/// Discovers all supported benchmark files under the provided roots.
pub(crate) fn discover_cases(roots: &[PathBuf]) -> Result<Vec<DiscoveredCase>, String> {
    let mut manifest_cache = BTreeMap::<PathBuf, Arc<Vec<ExpectationRule>>>::new();
    let mut seen = HashSet::<PathBuf>::new();
    let mut cases = Vec::new();

    for root in roots {
        if !root.exists() {
            return Err(format!("benchmark root does not exist: {}", root.display()));
        }
        if root.is_file() {
            maybe_push_case(root, &mut cases, &mut seen, &mut manifest_cache)?;
        } else {
            for entry in WalkDir::new(root).follow_links(false) {
                let entry = entry
                    .map_err(|error| format!("walk error under {}: {error}", root.display()))?;
                if entry.file_type().is_file() {
                    maybe_push_case(entry.path(), &mut cases, &mut seen, &mut manifest_cache)?;
                }
            }
        }
    }

    cases.sort_by_key(|case| (Reverse(case.bytes()), case.absolute_path().to_path_buf()));
    Ok(cases)
}

/// Adds one supported case file to the discovery output if it was not seen yet.
fn maybe_push_case(
    path: &Path,
    cases: &mut Vec<DiscoveredCase>,
    seen: &mut HashSet<PathBuf>,
    manifest_cache: &mut BTreeMap<PathBuf, Arc<Vec<ExpectationRule>>>,
) -> Result<(), String> {
    if !is_supported_case(path) {
        return Ok(());
    }

    let canonical = fs::canonicalize(path)
        .map_err(|error| format!("failed to canonicalize {}: {error}", path.display()))?;
    if !seen.insert(canonical.clone()) {
        return Ok(());
    }

    let manifest_root = find_manifest_root(path).unwrap_or_else(|| {
        path.parent()
            .unwrap_or_else(|| Path::new("."))
            .to_path_buf()
    });
    let rules = if let Some(rules) = manifest_cache.get(&manifest_root) {
        Arc::clone(rules)
    } else {
        let loaded = Arc::new(load_expectation_rules(&manifest_root)?);
        manifest_cache.insert(manifest_root.clone(), Arc::clone(&loaded));
        loaded
    };

    let display_path = path
        .strip_prefix(&manifest_root)
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned();
    let (default_expected, _source) = lookup_expectation(&display_path, &rules);
    let input = read_case_text(&canonical)?;
    let mut metadata = parse_trace_metadata(&input)?;
    if metadata.expected_queries.is_empty() {
        if let Some(expected) = default_expected {
            metadata.expected_queries.push(ExpectedQueryResult {
                query_index: 0,
                expected,
            });
        }
    } else if let Some(expected) = default_expected {
        for query in &mut metadata.expected_queries {
            if query.expected == QueryAnswer::Unknown {
                query.expected = expected;
            }
        }
    }

    let bytes = fs::metadata(&canonical)
        .map_err(|error| format!("failed to stat {}: {error}", canonical.display()))?
        .len();
    let query_count = Some(metadata.expected_queries.len());
    cases.push(DiscoveredCase::new(
        canonical,
        CaseRecord {
            key: display_path.clone().into_boxed_str(),
            bytes,
            logic: metadata.logic,
            query_count,
        },
        metadata.expected_queries,
    ));
    Ok(())
}

/// Returns `true` when the file suffix is a supported SMT-LIB case format.
fn is_supported_case(path: &Path) -> bool {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    name.ends_with(".smt2") || name.ends_with(".smt2.gz") || name.ends_with(".smt2.bz2")
}

/// Finds the nearest ancestor directory that contains an expectations manifest.
fn find_manifest_root(path: &Path) -> Option<PathBuf> {
    let search_start = if path.is_dir() { path } else { path.parent()? };
    search_start
        .ancestors()
        .find(|ancestor| ancestor.join(EXPECTATIONS_FILE).is_file())
        .map(Path::to_path_buf)
}

/// Loads all expectations rules from one manifest directory.
fn load_expectation_rules(root: &Path) -> Result<Vec<ExpectationRule>, String> {
    let manifest = root.join(EXPECTATIONS_FILE);
    if !manifest.is_file() {
        return Ok(Vec::new());
    }

    let content = fs::read_to_string(&manifest)
        .map_err(|error| format!("failed to read {}: {error}", manifest.display()))?;
    let mut rules = Vec::new();
    for (index, raw_line) in content.lines().enumerate() {
        let line = raw_line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let parts: Vec<&str> = line.split('\t').collect();
        if parts.len() != 3 {
            return Err(format!(
                "bad manifest row {} in {}: expected 3 tab-separated columns",
                index + 1,
                manifest.display()
            ));
        }
        rules.push(ExpectationRule {
            prefix: parts[0].into(),
            expected: QueryAnswer::parse(parts[1])?,
            source: parts[2].into(),
        });
    }
    rules.sort_by_key(|rule| Reverse(rule.prefix.len()));
    Ok(rules)
}

/// Looks up the longest matching expectation rule for one discovered path.
fn lookup_expectation(
    display_path: &str,
    rules: &[ExpectationRule],
) -> (Option<QueryAnswer>, Option<Box<str>>) {
    for rule in rules {
        if display_path.starts_with(rule.prefix.as_ref()) {
            return (Some(rule.expected), Some(rule.source.clone()));
        }
    }
    (None, None)
}

/// Reads one benchmark file, transparently decompressing gzip and bzip2 inputs.
fn read_case_text(path: &Path) -> Result<String, String> {
    let mut text = String::new();
    if has_suffix(path, ".gz") {
        let file = File::open(path)
            .map_err(|error| format!("failed to open {}: {error}", path.display()))?;
        let mut decoder = MultiGzDecoder::new(file);
        decoder
            .read_to_string(&mut text)
            .map_err(|error| format!("failed to decode gzip {}: {error}", path.display()))?;
    } else if has_suffix(path, ".bz2") {
        let file = File::open(path)
            .map_err(|error| format!("failed to open {}: {error}", path.display()))?;
        let mut decoder = BzDecoder::new(file);
        decoder
            .read_to_string(&mut text)
            .map_err(|error| format!("failed to decode bzip2 {}: {error}", path.display()))?;
    } else {
        let mut file = File::open(path)
            .map_err(|error| format!("failed to open {}: {error}", path.display()))?;
        file.read_to_string(&mut text)
            .map_err(|error| format!("failed to read {}: {error}", path.display()))?;
    }
    Ok(text)
}

/// Returns `true` when the path ends with the provided suffix.
fn has_suffix(path: &Path, suffix: &str) -> bool {
    path.file_name()
        .and_then(|name| name.to_str())
        .is_some_and(|name| name.ends_with(suffix))
}

/// Extracts the logic and expected query answers from one SMT-LIB trace.
fn parse_trace_metadata(input: &str) -> Result<TraceMetadata, String> {
    let tokens = tokenize(input);
    let (exprs, next) = parse_many(&tokens, 0)?;
    if next != tokens.len() {
        return Err("trailing tokens after trace parse".to_owned());
    }

    let mut metadata = TraceMetadata::default();
    let mut pending_status = None;
    for expr in exprs {
        let SExpr::List(items) = expr else {
            continue;
        };
        let Some(SExpr::Atom(head)) = items.first() else {
            continue;
        };
        match head.as_ref() {
            "set-logic" => {
                if let [_, SExpr::Atom(logic)] = items.as_slice() {
                    metadata.logic = Some(logic.clone());
                }
            }
            "set-info" => {
                if let [_, SExpr::Atom(keyword), SExpr::Atom(value)] = items.as_slice()
                    && keyword.as_ref() == ":status"
                {
                    pending_status = Some(QueryAnswer::parse(value)?);
                }
            }
            "check-sat" => {
                metadata.expected_queries.push(ExpectedQueryResult {
                    query_index: metadata.expected_queries.len(),
                    expected: pending_status.take().unwrap_or(QueryAnswer::Unknown),
                });
            }
            _ => {}
        }
    }
    Ok(metadata)
}

/// Counts `check-sat` queries in one SMT-LIB trace without re-reading the file.
pub(crate) fn query_count(input: &str) -> Result<usize, String> {
    parse_trace_metadata(input).map(|metadata| metadata.expected_queries.len())
}

/// One parsed S-expression.
#[derive(Clone, Debug, Eq, PartialEq)]
enum SExpr {
    /// One atom token.
    Atom(Box<str>),
    /// One list form.
    List(Vec<SExpr>),
}

/// Tokenizes one SMT-LIB input string into atoms and parentheses.
fn tokenize(input: &str) -> Vec<Box<str>> {
    let mut tokens = Vec::new();
    let mut current = String::new();
    let mut chars = input.chars().peekable();

    while let Some(ch) = chars.next() {
        if ch == ';' {
            while let Some(next) = chars.peek() {
                if *next == '\n' {
                    break;
                }
                chars.next();
            }
            continue;
        }
        match ch {
            '(' | ')' => {
                if !current.is_empty() {
                    tokens.push(current.clone().into_boxed_str());
                    current.clear();
                }
                tokens.push(ch.to_string().into_boxed_str());
            }
            ch if ch.is_whitespace() => {
                if !current.is_empty() {
                    tokens.push(current.clone().into_boxed_str());
                    current.clear();
                }
            }
            _ => current.push(ch),
        }
    }
    if !current.is_empty() {
        tokens.push(current.into_boxed_str());
    }
    tokens
}

/// Parses as many S-expressions as possible starting at `start`.
fn parse_many(tokens: &[Box<str>], mut start: usize) -> Result<(Vec<SExpr>, usize), String> {
    let mut exprs = Vec::new();
    while start < tokens.len() {
        if tokens[start].as_ref() == ")" {
            break;
        }
        let (expr, next) = parse_one(tokens, start)?;
        exprs.push(expr);
        start = next;
    }
    Ok((exprs, start))
}

/// Parses one S-expression starting at `start`.
fn parse_one(tokens: &[Box<str>], start: usize) -> Result<(SExpr, usize), String> {
    let token = tokens
        .get(start)
        .ok_or_else(|| "unexpected end of input".to_owned())?;
    if token.as_ref() == "(" {
        let (items, next) = parse_many(tokens, start + 1)?;
        if tokens.get(next).map(|token| token.as_ref()) != Some(")") {
            return Err("missing closing `)`".to_owned());
        }
        return Ok((SExpr::List(items), next + 1));
    }
    if token.as_ref() == ")" {
        return Err("unexpected `)`".to_owned());
    }
    Ok((SExpr::Atom(token.clone()), start + 1))
}
