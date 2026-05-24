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

use crate::model::{CaseRecord, DiscoveredCase, ExpectationRule, ExpectedQueryResult, QueryAnswer};

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
    let mut metadata = TraceMetadata::default();
    let mut pending_status = None;
    let mut scanner = MetadataScanner::new(input);
    let mut depth = 0usize;
    let mut command = None;

    while let Some(token) = scanner.next_token()? {
        match token {
            MetadataToken::OpenParen => {
                depth += 1;
                if depth == 1 {
                    command = Some(TopLevelCommand::default());
                } else if depth == 2
                    && let Some(command) = command.as_mut()
                {
                    command.has_nested_child = true;
                }
            }
            MetadataToken::CloseParen => {
                let Some(next_depth) = depth.checked_sub(1) else {
                    return Err("unexpected `)`".to_owned());
                };
                if depth == 1
                    && let Some(command) = command.take()
                {
                    apply_top_level_command(command, &mut metadata, &mut pending_status)?;
                }
                depth = next_depth;
            }
            MetadataToken::Atom(atom) => {
                if depth == 1
                    && let Some(command) = command.as_mut()
                {
                    command.direct_atoms.push(atom);
                }
            }
        }
    }
    if depth != 0 {
        return Err("missing closing `)`".to_owned());
    }
    Ok(metadata)
}

/// Counts `check-sat` queries in one SMT-LIB trace without re-reading the file.
pub(crate) fn query_count(input: &str) -> Result<usize, String> {
    parse_trace_metadata(input).map(|metadata| metadata.expected_queries.len())
}

/// One token relevant to the metadata scanner.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum MetadataToken<'a> {
    /// One opening parenthesis.
    OpenParen,
    /// One closing parenthesis.
    CloseParen,
    /// One atom token borrowed from the input.
    Atom(&'a str),
}

/// The direct children observed inside one top-level SMT-LIB command.
#[derive(Debug, Default)]
struct TopLevelCommand<'a> {
    /// All direct atom children, including the command head.
    direct_atoms: Vec<&'a str>,
    /// Whether the command contains any direct nested list child.
    has_nested_child: bool,
}

/// A lightweight token scanner that borrows atoms from the original input.
#[derive(Debug)]
struct MetadataScanner<'a> {
    /// The UTF-8 bytes of the input being scanned.
    input: &'a [u8],
    /// The next unread byte offset.
    index: usize,
}

impl<'a> MetadataScanner<'a> {
    /// Creates a new scanner over one SMT-LIB input string.
    fn new(input: &'a str) -> Self {
        Self {
            input: input.as_bytes(),
            index: 0,
        }
    }

    /// Returns the next token, skipping whitespace and comments.
    fn next_token(&mut self) -> Result<Option<MetadataToken<'a>>, String> {
        self.skip_layout();
        let Some(&byte) = self.input.get(self.index) else {
            return Ok(None);
        };
        match byte {
            b'(' => {
                self.index += 1;
                Ok(Some(MetadataToken::OpenParen))
            }
            b')' => {
                self.index += 1;
                Ok(Some(MetadataToken::CloseParen))
            }
            b'"' => self.scan_quoted_string().map(Some),
            b'|' => self.scan_quoted_symbol().map(Some),
            _ => self.scan_bare_atom().map(Some),
        }
    }

    /// Skips ASCII whitespace and semicolon comments.
    fn skip_layout(&mut self) {
        loop {
            while self
                .input
                .get(self.index)
                .is_some_and(|byte| byte.is_ascii_whitespace())
            {
                self.index += 1;
            }
            if self.input.get(self.index) != Some(&b';') {
                break;
            }
            self.index += 1;
            while let Some(&byte) = self.input.get(self.index) {
                self.index += 1;
                if byte == b'\n' {
                    break;
                }
            }
        }
    }

    /// Scans one SMT-LIB quoted string, preserving the borrowed source slice.
    fn scan_quoted_string(&mut self) -> Result<MetadataToken<'a>, String> {
        let start = self.index;
        self.index += 1;
        while let Some(&byte) = self.input.get(self.index) {
            self.index += 1;
            if byte == b'"' {
                if self.input.get(self.index) == Some(&b'"') {
                    self.index += 1;
                    continue;
                }
                return self.atom_from_range(start, self.index);
            }
        }
        Err("unterminated string literal".to_owned())
    }

    /// Scans one SMT-LIB quoted symbol, preserving the borrowed source slice.
    fn scan_quoted_symbol(&mut self) -> Result<MetadataToken<'a>, String> {
        let start = self.index;
        self.index += 1;
        while let Some(&byte) = self.input.get(self.index) {
            self.index += 1;
            if byte == b'\\' {
                if self.input.get(self.index).is_some() {
                    self.index += 1;
                }
                continue;
            }
            if byte == b'|' {
                return self.atom_from_range(start, self.index);
            }
        }
        Err("unterminated quoted symbol".to_owned())
    }

    /// Scans one non-quoted atom token.
    fn scan_bare_atom(&mut self) -> Result<MetadataToken<'a>, String> {
        let start = self.index;
        while let Some(&byte) = self.input.get(self.index) {
            if byte.is_ascii_whitespace() || matches!(byte, b'(' | b')' | b';') {
                break;
            }
            self.index += 1;
        }
        self.atom_from_range(start, self.index)
    }

    /// Converts one byte range back into a borrowed UTF-8 atom token.
    fn atom_from_range(&self, start: usize, end: usize) -> Result<MetadataToken<'a>, String> {
        let atom = std::str::from_utf8(&self.input[start..end]).map_err(|error| {
            format!("invalid utf-8 in trace metadata token at byte {start}: {error}")
        })?;
        Ok(MetadataToken::Atom(atom))
    }
}

/// Applies one fully scanned top-level command to the running metadata state.
fn apply_top_level_command(
    command: TopLevelCommand<'_>,
    metadata: &mut TraceMetadata,
    pending_status: &mut Option<QueryAnswer>,
) -> Result<(), String> {
    if command.has_nested_child {
        return Ok(());
    }
    match command.direct_atoms.as_slice() {
        ["set-logic", logic] => {
            metadata.logic = Some((*logic).into());
        }
        ["set-info", ":status", value] => {
            *pending_status = Some(QueryAnswer::parse(value)?);
        }
        ["check-sat"] => {
            metadata.expected_queries.push(ExpectedQueryResult {
                query_index: metadata.expected_queries.len(),
                expected: pending_status.take().unwrap_or(QueryAnswer::Unknown),
            });
        }
        _ => {}
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::{TraceMetadata, parse_trace_metadata, query_count};
    use crate::model::QueryAnswer;

    /// Ensures metadata scanning stays driven by top-level commands only.
    #[test]
    fn parse_trace_metadata_tracks_logic_and_pending_status() {
        let metadata = parse_trace_metadata(
            r#"
            ; Ignore comments and nested check-sat text.
            (set-info :notes "quoted ; comment (check-sat)")
            (set-logic QF_UF)
            (push 1)
            (set-info :status sat)
            (assert (= |symbol with spaces| |symbol with spaces|))
            (check-sat)
            (set-info :status unsat)
            (check-sat)
            (check-sat)
            "#,
        )
        .expect("parse metadata");
        assert_eq!(metadata.logic.as_deref(), Some("QF_UF"));
        assert_eq!(
            metadata
                .expected_queries
                .iter()
                .map(|query| query.expected)
                .collect::<Vec<_>>(),
            vec![QueryAnswer::Sat, QueryAnswer::Unsat, QueryAnswer::Unknown]
        );
    }

    /// Ensures nested list children do not get mistaken for simple top-level forms.
    #[test]
    fn parse_trace_metadata_ignores_non_flat_top_level_commands() {
        let metadata =
            parse_trace_metadata("(set-info (:status sat)) (check-sat)").expect("parse metadata");
        assert_eq!(metadata.expected_queries.len(), 1);
        assert_eq!(metadata.expected_queries[0].expected, QueryAnswer::Unknown);
    }

    /// Ensures query counting still reuses the metadata parser behavior.
    #[test]
    fn query_count_counts_each_top_level_check_sat() {
        let count =
            query_count("(check-sat) foo (check-sat) (assert (check-sat))").expect("count queries");
        assert_eq!(count, 2);
    }

    /// Ensures malformed inputs still fail fast instead of silently undercounting.
    #[test]
    fn parse_trace_metadata_rejects_unbalanced_or_unterminated_input() {
        assert!(parse_trace_metadata("(check-sat").is_err());
        assert!(parse_trace_metadata(r#"(set-info :notes "oops)"#).is_err());
        assert!(parse_trace_metadata("(check-sat))").is_err());
    }

    /// Keeps the parser return type referenced so missing-docs applies to the tests too.
    #[test]
    fn parse_trace_metadata_returns_default_for_irrelevant_input() {
        let metadata = parse_trace_metadata("atom-only").expect("parse metadata");
        assert_eq!(metadata.logic, TraceMetadata::default().logic);
        assert!(metadata.expected_queries.is_empty());
    }
}
