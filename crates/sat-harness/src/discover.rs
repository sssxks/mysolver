//! Benchmark discovery and expectation-manifest loading.

use std::cmp::Reverse;
use std::collections::{BTreeMap, HashSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;

use walkdir::WalkDir;

use crate::model::{CaseSpec, ExpectationRule, ExpectedResult};

/// The hidden manifest file used to attach expected results to benchmark paths.
const EXPECTATIONS_FILE: &str = "expectations.tsv";

/// Discovers all supported benchmark files under the provided roots.
pub(crate) fn discover_cases(roots: &[PathBuf]) -> Result<Vec<CaseSpec>, String> {
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

    cases.sort_by_key(|case| (Reverse(case.bytes), case.display_path.clone()));
    Ok(cases)
}

/// Adds one supported case file to the discovery output if it was not seen yet.
fn maybe_push_case(
    path: &Path,
    cases: &mut Vec<CaseSpec>,
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
    let (expected, source) = lookup_expectation(&display_path, &rules);
    let bytes = fs::metadata(&canonical)
        .map_err(|error| format!("failed to stat {}: {error}", canonical.display()))?
        .len();
    cases.push(CaseSpec {
        absolute_path: canonical,
        display_path: display_path.into_boxed_str(),
        bytes,
        expected,
        source,
    });
    Ok(())
}

/// Returns `true` when the file suffix is a supported DIMACS case format.
fn is_supported_case(path: &Path) -> bool {
    let Some(name) = path.file_name().and_then(|name| name.to_str()) else {
        return false;
    };
    name.ends_with(".cnf")
        || name.ends_with(".dimacs")
        || name.ends_with(".cnf.gz")
        || name.ends_with(".dimacs.gz")
        || name.ends_with(".cnf.bz2")
        || name.ends_with(".dimacs.bz2")
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
            expected: ExpectedResult::parse(parts[1])?,
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
) -> (Option<ExpectedResult>, Option<Box<str>>) {
    for rule in rules {
        if display_path.starts_with(rule.prefix.as_ref()) {
            return (Some(rule.expected), Some(rule.source.clone()));
        }
    }
    (None, None)
}
