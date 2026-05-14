//! A subprocess-isolated benchmark harness for the `sat` solver.
//!
//! The parent process discovers benchmark inputs, runs one benchmark per child
//! process, enforces wall-clock timeouts, and renders a friendly terminal view.
//! Each child process loads exactly one DIMACS case and emits a compact JSON
//! report so that panics, signals, and out-of-memory kills stay isolated.

use std::cmp::Reverse;
use std::collections::{BTreeMap, HashSet, VecDeque};
use std::env;
use std::fs::{self, File};
use std::io::{self, IsTerminal, Read};
use std::num::NonZeroUsize;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};
use std::sync::mpsc;
use std::sync::{Arc, Mutex};
use std::thread;
use std::time::{Duration, Instant};

use bzip2::read::BzDecoder;
use clap::{Args, Parser, Subcommand};
use console::style;
use flate2::read::MultiGzDecoder;
use indicatif::{HumanCount, HumanDuration, ProgressBar, ProgressDrawTarget, ProgressStyle};
use sat::{SatResult as SolverSatResult, Solver, parse_dimacs};
use serde::{Deserialize, Serialize};
use tempfile::NamedTempFile;
use walkdir::WalkDir;

/// The hidden manifest file used to attach expected results to benchmark paths.
const EXPECTATIONS_FILE: &str = "expectations.tsv";

/// The benchmark runner command line.
#[derive(Debug, Parser)]
#[command(
    author,
    version,
    about = "Run SAT benchmarks with subprocess isolation and live progress output."
)]
struct Cli {
    /// The subcommand to execute.
    #[command(subcommand)]
    command: HarnessCommand,
}

/// All supported harness subcommands.
#[derive(Debug, Subcommand)]
enum HarnessCommand {
    /// Discover and execute benchmark cases.
    Run(RunArgs),
    /// Run one benchmark case in an isolated child process.
    #[command(hide = true, name = "__internal-run-case")]
    InternalRunCase(InternalRunCaseArgs),
}

/// Arguments for the user-facing `run` command.
#[derive(Debug, Args)]
struct RunArgs {
    /// Benchmark roots to scan.
    ///
    /// When omitted, the harness scans `test/fixture/sat`.
    roots: Vec<PathBuf>,
    /// The number of child processes to run concurrently.
    #[arg(short, long)]
    jobs: Option<NonZeroUsize>,
    /// The per-case timeout.
    #[arg(short, long, default_value = "30s", value_parser = parse_timeout)]
    timeout: Duration,
    /// The number of slowest cases to print in the final summary.
    #[arg(long, default_value_t = 10)]
    slowest: usize,
}

/// Arguments for the hidden child-process entrypoint.
#[derive(Debug, Args)]
struct InternalRunCaseArgs {
    /// The case file to execute.
    #[arg(long)]
    case: PathBuf,
    /// The JSON report written back to the parent process.
    #[arg(long)]
    report: PathBuf,
}

/// One expected solver answer loaded from an expectations manifest.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum ExpectedResult {
    /// The case is expected to be satisfiable.
    Sat,
    /// The case is expected to be unsatisfiable.
    Unsat,
}

impl ExpectedResult {
    /// Parses a manifest token into an expected-answer label.
    fn parse(text: &str) -> Result<Self, String> {
        match text {
            "sat" => Ok(Self::Sat),
            "unsat" => Ok(Self::Unsat),
            _ => Err(format!("unsupported expectation label: {text}")),
        }
    }

    /// Returns the lowercase display label used in the terminal.
    fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
        }
    }
}

/// One expectations rule loaded from `expectations.tsv`.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ExpectationRule {
    /// The path prefix, relative to the manifest directory.
    prefix: Box<str>,
    /// The expected solver answer for matching paths.
    expected: ExpectedResult,
    /// A short human-readable source label.
    source: Box<str>,
}

/// A benchmark case discovered on disk.
#[derive(Clone, Debug)]
struct CaseSpec {
    /// The canonical absolute file path passed to the child process.
    absolute_path: PathBuf,
    /// The path displayed in progress output and summaries.
    display_path: Box<str>,
    /// The file size in bytes used to sort long cases first.
    bytes: u64,
    /// The optional oracle answer for correctness checking.
    expected: Option<ExpectedResult>,
    /// The optional source label that provided the oracle answer.
    source: Option<Box<str>>,
}

/// The structured report produced by a child process.
#[derive(Debug, Serialize, Deserialize)]
struct ChildReport {
    /// The child-level outcome.
    kind: ChildReportKind,
    /// The number of variables loaded from the DIMACS case.
    variables: usize,
    /// The total child runtime in milliseconds.
    elapsed_millis: u64,
}

/// All structured outcomes that can be reported by the child process.
#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "type", content = "detail")]
enum ChildReportKind {
    /// The solver returned `SAT`.
    Sat,
    /// The solver returned `UNSAT`.
    Unsat,
    /// The DIMACS input could not be parsed.
    ParseError(String),
    /// The case file could not be loaded from disk.
    InputError(String),
}

/// One completed case outcome received by the parent process.
#[derive(Debug)]
struct CaseOutcome {
    /// The original benchmark metadata.
    case: CaseSpec,
    /// The wall-clock runtime measured by the parent process.
    elapsed: Duration,
    /// The classified result category.
    category: OutcomeCategory,
    /// An optional actual solver answer.
    actual: Option<ExpectedResult>,
    /// An optional detail string for failures and summaries.
    detail: Option<Box<str>>,
    /// The number of variables loaded by the child, if available.
    variables: Option<usize>,
}

/// The top-level result category used in summaries and exit codes.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
enum OutcomeCategory {
    /// The solver answer matched the oracle.
    Pass,
    /// The solver finished, but the case had no oracle answer.
    NoOracle,
    /// The solver returned the wrong answer.
    WrongAnswer,
    /// The DIMACS input was rejected by the parser.
    ParseError,
    /// The child exceeded the configured timeout.
    Timeout,
    /// The child process panicked.
    Panic,
    /// The child process was killed by a signal.
    Killed,
    /// The harness itself encountered an infrastructure error.
    HarnessError,
}

impl OutcomeCategory {
    /// Returns `true` when the category should fail the overall run.
    fn is_failure(self) -> bool {
        !matches!(self, Self::Pass | Self::NoOracle)
    }

    /// Returns the short uppercase label used in the terminal.
    fn label(self) -> &'static str {
        match self {
            Self::Pass => "PASS",
            Self::NoOracle => "DONE",
            Self::WrongAnswer => "WRONG",
            Self::ParseError => "PARSE",
            Self::Timeout => "TIME",
            Self::Panic => "PANIC",
            Self::Killed => "KILLED",
            Self::HarnessError => "ERROR",
        }
    }
}

/// Aggregate counters shown in the progress bar and final summary.
#[derive(Debug, Default)]
struct OutcomeStats {
    /// The number of completed cases.
    done: usize,
    /// The number of passing cases with an oracle answer.
    pass: usize,
    /// The number of completed cases without an oracle answer.
    no_oracle: usize,
    /// The number of wrong answers.
    wrong: usize,
    /// The number of parse errors.
    parse: usize,
    /// The number of timeouts.
    timeout: usize,
    /// The number of panics.
    panic: usize,
    /// The number of signal-killed children.
    killed: usize,
    /// The number of harness infrastructure failures.
    harness: usize,
}

impl OutcomeStats {
    /// Records one completed outcome.
    fn record(&mut self, category: OutcomeCategory) {
        self.done += 1;
        match category {
            OutcomeCategory::Pass => self.pass += 1,
            OutcomeCategory::NoOracle => self.no_oracle += 1,
            OutcomeCategory::WrongAnswer => self.wrong += 1,
            OutcomeCategory::ParseError => self.parse += 1,
            OutcomeCategory::Timeout => self.timeout += 1,
            OutcomeCategory::Panic => self.panic += 1,
            OutcomeCategory::Killed => self.killed += 1,
            OutcomeCategory::HarnessError => self.harness += 1,
        }
    }

    /// Returns `true` when at least one failing outcome was recorded.
    fn has_failures(&self) -> bool {
        self.wrong > 0
            || self.parse > 0
            || self.timeout > 0
            || self.panic > 0
            || self.killed > 0
            || self.harness > 0
    }
}

/// The final parent-process summary returned from `run`.
#[derive(Debug)]
struct RunSummary {
    /// The final counters for all outcomes.
    stats: OutcomeStats,
}

/// Runs the selected harness subcommand.
fn main() -> ExitCode {
    match run_command(Cli::parse()) {
        Ok(summary) => {
            if summary.stats.has_failures() {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            }
        }
        Err(error) => {
            eprintln!("{} {error}", style("error").red().bold());
            ExitCode::from(2)
        }
    }
}

/// Dispatches one parsed CLI command.
fn run_command(cli: Cli) -> Result<RunSummary, String> {
    match cli.command {
        HarnessCommand::Run(args) => run_parent(args),
        HarnessCommand::InternalRunCase(args) => {
            run_child(args)?;
            Ok(RunSummary {
                stats: OutcomeStats::default(),
            })
        }
    }
}

/// Executes the top-level parent harness flow.
fn run_parent(args: RunArgs) -> Result<RunSummary, String> {
    let requested_roots = if args.roots.is_empty() {
        vec![PathBuf::from("test/fixture/sat")]
    } else {
        args.roots
    };
    let cases = discover_cases(&requested_roots)?;
    if cases.is_empty() {
        return Err("no supported benchmark cases were found".to_string());
    }

    let jobs = args
        .jobs
        .unwrap_or_else(default_jobs)
        .get()
        .min(cases.len())
        .max(1);
    let total = cases.len();
    let current_exe = env::current_exe()
        .map_err(|error| format!("failed to locate current executable: {error}"))?;
    let queue = Arc::new(Mutex::new(VecDeque::from(cases)));
    let (sender, receiver) = mpsc::channel();
    let mut handles = Vec::with_capacity(jobs);

    for _ in 0..jobs {
        let worker_queue = Arc::clone(&queue);
        let worker_sender = sender.clone();
        let worker_exe = current_exe.clone();
        let timeout = args.timeout;
        handles.push(thread::spawn(move || {
            worker_loop(worker_queue, worker_sender, worker_exe, timeout);
        }));
    }
    drop(sender);

    let interactive = io::stderr().is_terminal();
    let progress_bar = build_progress_bar(total, interactive);
    if !interactive {
        eprintln!(
            "running {} cases with {} workers (timeout {})",
            HumanCount(total as u64),
            HumanCount(jobs as u64),
            HumanDuration(args.timeout),
        );
    }

    let started = Instant::now();
    let mut outcomes = Vec::with_capacity(total);
    let mut stats = OutcomeStats::default();

    for outcome in receiver {
        stats.record(outcome.category);
        progress_bar.inc(1);
        progress_bar.set_message(progress_message(&stats, jobs));
        if outcome.category.is_failure() {
            let rendered = format_failure(&outcome);
            if interactive {
                progress_bar.println(rendered);
            } else {
                eprintln!("{rendered}");
            }
        }
        outcomes.push(outcome);
    }

    for handle in handles {
        handle
            .join()
            .map_err(|_| "worker thread panicked in parent harness".to_string())?;
    }

    let elapsed = started.elapsed();
    progress_bar.finish_and_clear();
    print_summary(&outcomes, &stats, elapsed, jobs, args.slowest);
    Ok(RunSummary { stats })
}

/// Repeatedly executes cases from the shared queue until all work is exhausted.
fn worker_loop(
    queue: Arc<Mutex<VecDeque<CaseSpec>>>,
    sender: mpsc::Sender<CaseOutcome>,
    current_exe: PathBuf,
    timeout: Duration,
) {
    loop {
        let next_case = match queue.lock() {
            Ok(mut queue) => queue.pop_front(),
            Err(_) => None,
        };
        let Some(case) = next_case else {
            break;
        };
        let outcome = run_case_subprocess(&current_exe, case, timeout);
        if sender.send(outcome).is_err() {
            break;
        }
    }
}

/// Executes one case in a fresh child process and classifies its outcome.
fn run_case_subprocess(current_exe: &Path, case: CaseSpec, timeout: Duration) -> CaseOutcome {
    let started = Instant::now();
    let report_file = match NamedTempFile::new() {
        Ok(file) => file,
        Err(error) => {
            return harness_error(case, started.elapsed(), format!("tempfile error: {error}"));
        }
    };
    let stderr_file = match NamedTempFile::new() {
        Ok(file) => file,
        Err(error) => {
            return harness_error(case, started.elapsed(), format!("tempfile error: {error}"));
        }
    };
    let stderr_stdio = match stderr_file.reopen() {
        Ok(file) => Stdio::from(file),
        Err(error) => {
            return harness_error(
                case,
                started.elapsed(),
                format!("stderr capture error: {error}"),
            );
        }
    };

    let mut child = match Command::new(current_exe)
        .arg("__internal-run-case")
        .arg("--case")
        .arg(&case.absolute_path)
        .arg("--report")
        .arg(report_file.path())
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(stderr_stdio)
        .spawn()
    {
        Ok(child) => child,
        Err(error) => {
            return harness_error(case, started.elapsed(), format!("spawn error: {error}"));
        }
    };

    let mut timed_out = false;
    let status = loop {
        match child.try_wait() {
            Ok(Some(status)) => break status,
            Ok(None) => {
                if started.elapsed() >= timeout {
                    timed_out = true;
                    let _ = child.kill();
                    match child.wait() {
                        Ok(status) => break status,
                        Err(error) => {
                            return harness_error(
                                case,
                                started.elapsed(),
                                format!("failed to wait after timeout: {error}"),
                            );
                        }
                    }
                }
                thread::sleep(Duration::from_millis(10));
            }
            Err(error) => {
                return harness_error(case, started.elapsed(), format!("wait error: {error}"));
            }
        }
    };

    let elapsed = started.elapsed();
    if timed_out {
        return CaseOutcome {
            case,
            elapsed,
            category: OutcomeCategory::Timeout,
            actual: None,
            detail: Some(format!("timed out after {}", humantime::format_duration(timeout)).into()),
            variables: None,
        };
    }

    let stderr = fs::read_to_string(stderr_file.path()).unwrap_or_default();
    let report_text = fs::read_to_string(report_file.path()).ok();
    classify_child_completion(case, elapsed, status, report_text.as_deref(), &stderr)
}

/// Classifies a completed child process into a stable harness outcome.
fn classify_child_completion(
    case: CaseSpec,
    elapsed: Duration,
    status: std::process::ExitStatus,
    report_text: Option<&str>,
    stderr: &str,
) -> CaseOutcome {
    if status.success() {
        let Some(report_text) = report_text else {
            return harness_error(case, elapsed, "missing child report".to_string());
        };
        let report: ChildReport = match serde_json::from_str(report_text) {
            Ok(report) => report,
            Err(error) => {
                return harness_error(case, elapsed, format!("invalid child report: {error}"));
            }
        };
        return classify_report(case, elapsed, report);
    }

    let signal = exit_signal(status);
    let stderr = stderr.trim();
    if stderr.contains("panicked at") {
        return CaseOutcome {
            case,
            elapsed,
            category: OutcomeCategory::Panic,
            actual: None,
            detail: Some(trim_detail(stderr).into()),
            variables: None,
        };
    }

    if let Some(signal) = signal {
        let detail = if signal == 9 {
            "terminated by SIGKILL (possible OOM kill)".to_string()
        } else {
            format!("terminated by signal {signal}")
        };
        return CaseOutcome {
            case,
            elapsed,
            category: OutcomeCategory::Killed,
            actual: None,
            detail: Some(detail.into()),
            variables: None,
        };
    }

    let detail = match status.code() {
        Some(code) => {
            if stderr.is_empty() {
                format!("child exited with status code {code}")
            } else {
                format!(
                    "child exited with status code {code}: {}",
                    trim_detail(stderr)
                )
            }
        }
        None => "child exited without status code".to_string(),
    };
    harness_error(case, elapsed, detail)
}

/// Maps a structured child report onto the final parent outcome categories.
fn classify_report(case: CaseSpec, elapsed: Duration, report: ChildReport) -> CaseOutcome {
    match report.kind {
        ChildReportKind::Sat | ChildReportKind::Unsat => {
            let actual = match report.kind {
                ChildReportKind::Sat => ExpectedResult::Sat,
                ChildReportKind::Unsat => ExpectedResult::Unsat,
                ChildReportKind::ParseError(_) | ChildReportKind::InputError(_) => unreachable!(),
            };
            match case.expected {
                Some(expected) if expected == actual => CaseOutcome {
                    case,
                    elapsed,
                    category: OutcomeCategory::Pass,
                    actual: Some(actual),
                    detail: None,
                    variables: Some(report.variables),
                },
                Some(expected) => CaseOutcome {
                    detail: Some(
                        format!(
                            "expected {} from {}, got {}",
                            expected.as_str(),
                            case.source.as_deref().unwrap_or("manifest"),
                            actual.as_str()
                        )
                        .into(),
                    ),
                    case,
                    elapsed,
                    category: OutcomeCategory::WrongAnswer,
                    actual: Some(actual),
                    variables: Some(report.variables),
                },
                None => CaseOutcome {
                    case,
                    elapsed,
                    category: OutcomeCategory::NoOracle,
                    actual: Some(actual),
                    detail: None,
                    variables: Some(report.variables),
                },
            }
        }
        ChildReportKind::ParseError(error) => CaseOutcome {
            case,
            elapsed,
            category: OutcomeCategory::ParseError,
            actual: None,
            detail: Some(trim_detail(&error).into()),
            variables: Some(report.variables),
        },
        ChildReportKind::InputError(error) => harness_error(case, elapsed, error),
    }
}

/// Creates one infrastructure error outcome.
fn harness_error(case: CaseSpec, elapsed: Duration, detail: String) -> CaseOutcome {
    CaseOutcome {
        case,
        elapsed,
        category: OutcomeCategory::HarnessError,
        actual: None,
        detail: Some(detail.into()),
        variables: None,
    }
}

/// Discovers all supported benchmark files under the provided roots.
fn discover_cases(roots: &[PathBuf]) -> Result<Vec<CaseSpec>, String> {
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

/// Runs the hidden child process entrypoint and writes the structured report.
fn run_child(args: InternalRunCaseArgs) -> Result<(), String> {
    let started = Instant::now();
    let report = match load_case_and_solver(&args.case) {
        Ok(mut solver) => ChildReport {
            variables: solver.num_vars(),
            elapsed_millis: 0,
            kind: match solver.solve() {
                SolverSatResult::Sat => ChildReportKind::Sat,
                SolverSatResult::Unsat => ChildReportKind::Unsat,
            },
        },
        Err(LoadCaseError::Input(error)) => ChildReport {
            variables: 0,
            elapsed_millis: 0,
            kind: ChildReportKind::InputError(error),
        },
        Err(LoadCaseError::Parse(error, variables)) => ChildReport {
            variables,
            elapsed_millis: 0,
            kind: ChildReportKind::ParseError(error),
        },
    };
    let mut report = report;
    report.elapsed_millis = saturating_millis(started.elapsed());
    let payload = serde_json::to_vec(&report)
        .map_err(|error| format!("failed to serialize child report: {error}"))?;
    fs::write(&args.report, payload).map_err(|error| {
        format!(
            "failed to write child report {}: {error}",
            args.report.display()
        )
    })
}

/// Loads one DIMACS case and builds a solver instance from it.
fn load_case_and_solver(path: &Path) -> Result<Solver, LoadCaseError> {
    let input = read_case_text(path).map_err(LoadCaseError::Input)?;
    parse_dimacs(&input).map_err(|error| LoadCaseError::Parse(error, extract_declared_vars(&input)))
}

/// All load failures handled inside the child process.
#[derive(Debug)]
enum LoadCaseError {
    /// The file could not be read or decompressed.
    Input(String),
    /// The text could be read, but DIMACS parsing failed.
    Parse(String, usize),
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

/// Extracts the declared variable count from a DIMACS problem line when present.
fn extract_declared_vars(input: &str) -> usize {
    input
        .lines()
        .map(str::trim)
        .find_map(|line| {
            let mut parts = line.split_whitespace();
            match (parts.next(), parts.next(), parts.next()) {
                (Some("p"), Some("cnf"), Some(vars)) => vars.parse::<usize>().ok(),
                _ => None,
            }
        })
        .unwrap_or(0)
}

/// Parses a user-provided timeout string such as `30s` or `250ms`.
fn parse_timeout(text: &str) -> Result<Duration, String> {
    humantime::parse_duration(text).map_err(|error| error.to_string())
}

/// Returns the default worker count based on the host CPU count.
fn default_jobs() -> NonZeroUsize {
    std::thread::available_parallelism().unwrap_or(NonZeroUsize::MIN)
}

/// Builds the live progress bar used by the parent process.
fn build_progress_bar(total: usize, interactive: bool) -> ProgressBar {
    let draw_target = if interactive {
        ProgressDrawTarget::stderr_with_hz(10)
    } else {
        ProgressDrawTarget::hidden()
    };
    let progress_bar = ProgressBar::with_draw_target(Some(total as u64), draw_target);
    let style = ProgressStyle::with_template(
        "{spinner:.cyan} [{elapsed_precise}] {wide_bar:.cyan/blue} {pos:>6}/{len:6} {msg}",
    )
    .expect("valid progress template")
    .progress_chars("=>-");
    progress_bar.set_style(style);
    progress_bar.set_message("pass 0 | wrong 0 | timeout 0");
    progress_bar
}

/// Formats the live status counters shown beside the progress bar.
fn progress_message(stats: &OutcomeStats, jobs: usize) -> String {
    format!(
        "jobs {} | pass {} | no-oracle {} | wrong {} | parse {} | timeout {} | panic {} | killed {} | error {}",
        HumanCount(jobs as u64),
        HumanCount(stats.pass as u64),
        HumanCount(stats.no_oracle as u64),
        HumanCount(stats.wrong as u64),
        HumanCount(stats.parse as u64),
        HumanCount(stats.timeout as u64),
        HumanCount(stats.panic as u64),
        HumanCount(stats.killed as u64),
        HumanCount(stats.harness as u64),
    )
}

/// Formats a failure line that is printed immediately during the run.
fn format_failure(outcome: &CaseOutcome) -> String {
    let label = match outcome.category {
        OutcomeCategory::WrongAnswer => style(outcome.category.label()).red().bold(),
        OutcomeCategory::ParseError => style(outcome.category.label()).yellow().bold(),
        OutcomeCategory::Timeout => style(outcome.category.label()).yellow().bold(),
        OutcomeCategory::Panic => style(outcome.category.label()).magenta().bold(),
        OutcomeCategory::Killed => style(outcome.category.label()).red().bold(),
        OutcomeCategory::HarnessError => style(outcome.category.label()).red().bold(),
        OutcomeCategory::Pass | OutcomeCategory::NoOracle => {
            style(outcome.category.label()).green().bold()
        }
    };
    let detail = outcome.detail.as_deref().unwrap_or("no detail");
    format!(
        "{label} {:>10} {} :: {}",
        format_compact_duration(outcome.elapsed),
        outcome.case.display_path,
        detail,
    )
}

/// Prints the final run summary and the slowest cases.
fn print_summary(
    outcomes: &[CaseOutcome],
    stats: &OutcomeStats,
    elapsed: Duration,
    jobs: usize,
    slowest: usize,
) {
    let total = outcomes.len();
    let throughput = if elapsed.is_zero() {
        0.0
    } else {
        total as f64 / elapsed.as_secs_f64()
    };
    let divider = "─".repeat(78);
    eprintln!("{divider}");
    eprintln!(
        "{} in {} with {} workers",
        style("finished").cyan().bold(),
        format_compact_duration(elapsed),
        HumanCount(jobs as u64),
    );
    eprintln!(
        "cases: total {} | pass {} | no-oracle {} | wrong {} | parse {} | timeout {} | panic {} | killed {} | error {}",
        HumanCount(total as u64),
        HumanCount(stats.pass as u64),
        HumanCount(stats.no_oracle as u64),
        HumanCount(stats.wrong as u64),
        HumanCount(stats.parse as u64),
        HumanCount(stats.timeout as u64),
        HumanCount(stats.panic as u64),
        HumanCount(stats.killed as u64),
        HumanCount(stats.harness as u64),
    );
    eprintln!("throughput: {:.1} cases/s", throughput);

    if slowest > 0 {
        let mut ranked: Vec<&CaseOutcome> = outcomes.iter().collect();
        ranked.sort_by_key(|outcome| Reverse(outcome.elapsed));
        let limit = slowest.min(ranked.len());
        if limit > 0 {
            eprintln!("slowest cases:");
            for outcome in ranked.into_iter().take(limit) {
                let label = outcome
                    .actual
                    .map(ExpectedResult::as_str)
                    .unwrap_or_else(|| outcome.category.label());
                let variables = outcome
                    .variables
                    .map(|count| format!("vars {}", HumanCount(count as u64)))
                    .unwrap_or_else(|| "vars ?".to_string());
                eprintln!(
                    "  {:>10} {:<6} {} ({})",
                    format_compact_duration(outcome.elapsed),
                    label,
                    outcome.case.display_path,
                    variables,
                );
            }
        }
    }

    if stats.has_failures() {
        eprintln!("{}", style("run failed").red().bold());
    } else {
        eprintln!("{}", style("run passed").green().bold());
    }
}

/// Truncates long stderr and parser messages to a readable one-line detail.
fn trim_detail(text: &str) -> String {
    const LIMIT: usize = 160;
    let compact = text.replace('\n', " ");
    if compact.len() <= LIMIT {
        compact
    } else {
        format!("{}...", &compact[..LIMIT])
    }
}

/// Formats a duration using a short, benchmark-oriented representation.
fn format_compact_duration(duration: Duration) -> String {
    let seconds = duration.as_secs_f64();
    if seconds >= 60.0 {
        format!("{:.1}m", seconds / 60.0)
    } else if seconds >= 1.0 {
        format!("{seconds:.2}s")
    } else if duration.as_millis() > 0 {
        format!("{:.1}ms", seconds * 1_000.0)
    } else if duration.as_micros() > 0 {
        format!("{:.0}us", seconds * 1_000_000.0)
    } else {
        format!("{}ns", duration.as_nanos())
    }
}

/// Converts a duration into a saturating millisecond counter.
fn saturating_millis(duration: Duration) -> u64 {
    duration.as_millis().min(u128::from(u64::MAX)) as u64
}

/// Returns the terminating Unix signal for a child process, when available.
fn exit_signal(status: std::process::ExitStatus) -> Option<i32> {
    use std::os::unix::process::ExitStatusExt;

    status.signal()
}
