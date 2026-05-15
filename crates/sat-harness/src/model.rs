//! Shared data structures used across harness modules.

use std::path::PathBuf;
use std::time::Duration;

use serde::{Deserialize, Serialize};

/// One expected solver answer loaded from an expectations manifest.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub(crate) enum ExpectedResult {
    /// The case is expected to be satisfiable.
    Sat,
    /// The case is expected to be unsatisfiable.
    Unsat,
}

impl ExpectedResult {
    /// Parses a manifest token into an expected-answer label.
    pub(crate) fn parse(text: &str) -> Result<Self, String> {
        match text {
            "sat" => Ok(Self::Sat),
            "unsat" => Ok(Self::Unsat),
            _ => Err(format!("unsupported expectation label: {text}")),
        }
    }

    /// Returns the lowercase display label used in the terminal.
    pub(crate) fn as_str(self) -> &'static str {
        match self {
            Self::Sat => "sat",
            Self::Unsat => "unsat",
        }
    }
}

/// One expectations rule loaded from `expectations.tsv`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct ExpectationRule {
    /// The path prefix, relative to the manifest directory.
    pub(crate) prefix: Box<str>,
    /// The expected solver answer for matching paths.
    pub(crate) expected: ExpectedResult,
    /// A short human-readable source label.
    pub(crate) source: Box<str>,
}

/// A benchmark case discovered on disk.
#[derive(Clone, Debug)]
pub(crate) struct CaseSpec {
    /// The canonical absolute file path passed to the child process.
    pub(crate) absolute_path: PathBuf,
    /// The path displayed in progress output and summaries, truncated when long.
    pub(crate) display_path: Box<str>,
    /// The file size in bytes used to sort long cases first.
    pub(crate) bytes: u64,
    /// The optional oracle answer for correctness checking.
    pub(crate) expected: Option<ExpectedResult>,
    /// The optional source label that provided the oracle answer.
    pub(crate) source: Option<Box<str>>,
}

/// The structured report produced by a child process.
#[derive(Debug, Serialize, Deserialize)]
pub(crate) struct ChildReport {
    /// The child-level outcome.
    pub(crate) kind: ChildReportKind,
}

/// All structured outcomes that can be reported by the child process.
#[derive(Debug, Serialize, Deserialize)]
#[serde(rename_all = "snake_case", tag = "type", content = "detail")]
pub(crate) enum ChildReportKind {
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
pub(crate) struct CaseOutcome {
    /// The original benchmark metadata.
    pub(crate) case: CaseSpec,
    /// The wall-clock runtime measured by the parent process.
    pub(crate) elapsed: Duration,
    /// The classified result category.
    pub(crate) category: OutcomeCategory,
    /// An optional detail string for failures and summaries.
    pub(crate) detail: Option<Box<str>>,
}

/// The top-level result category used in summaries and exit codes.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub(crate) enum OutcomeCategory {
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
    pub(crate) fn is_failure(self) -> bool {
        !matches!(self, Self::Pass | Self::NoOracle)
    }

    /// Returns the short uppercase label used in the terminal.
    pub(crate) fn label(self) -> &'static str {
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
pub(crate) struct OutcomeStats {
    /// The number of completed cases.
    pub(crate) done: usize,
    /// The number of passing cases with an oracle answer.
    pub(crate) pass: usize,
    /// The number of completed cases without an oracle answer.
    pub(crate) no_oracle: usize,
    /// The number of wrong answers.
    pub(crate) wrong: usize,
    /// The number of parse errors.
    pub(crate) parse: usize,
    /// The number of timeouts.
    pub(crate) timeout: usize,
    /// The number of panics.
    pub(crate) panic: usize,
    /// The number of signal-killed children.
    pub(crate) killed: usize,
    /// The number of harness infrastructure failures.
    pub(crate) harness: usize,
}

impl OutcomeStats {
    /// Records one completed outcome.
    pub(crate) fn record(&mut self, category: OutcomeCategory) {
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
    pub(crate) fn has_failures(&self) -> bool {
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
pub(crate) struct RunSummary {
    /// The final counters for all outcomes.
    pub(crate) stats: OutcomeStats,
}
