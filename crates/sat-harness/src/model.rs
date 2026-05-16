//! Shared data structures used across harness modules.

use std::path::{Path, PathBuf};
use std::time::Duration;

use console::{StyledObject, style};
use sat::telemetry::{Sample, Summary};
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

/// The stable case metadata kept in saved harness result files.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct CaseRecord {
    /// The stable manifest-relative key used when comparing saved runs.
    pub(crate) key: Box<str>,
    /// The file size in bytes used to sort long cases first.
    pub(crate) bytes: u64,
    /// The optional oracle answer for correctness checking.
    pub(crate) expected: Option<ExpectedResult>,
    /// The optional source label that provided the oracle answer.
    pub(crate) source: Option<Box<str>>,
}

impl CaseRecord {
    /// Returns the stable key used when sorting or comparing saved runs.
    pub(crate) fn comparison_key(&self) -> &str {
        &self.key
    }
}

/// A benchmark case discovered on disk and ready to execute.
#[derive(Clone, Debug)]
pub(crate) struct DiscoveredCase {
    /// The canonical absolute file path passed to the child process.
    absolute_path: PathBuf,
    /// The stable case metadata that survives into saved result files.
    record: CaseRecord,
}

impl DiscoveredCase {
    /// Builds one discovered runtime case from its executable path and saved metadata.
    pub(crate) fn new(absolute_path: PathBuf, record: CaseRecord) -> Self {
        Self {
            absolute_path,
            record,
        }
    }

    /// Returns the canonical file path used to execute this case.
    pub(crate) fn absolute_path(&self) -> &Path {
        &self.absolute_path
    }

    /// Returns the file size used for discovery ordering.
    pub(crate) fn bytes(&self) -> u64 {
        self.record.bytes
    }

    /// Returns the stable case metadata borrowed from this runtime case.
    pub(crate) fn record(&self) -> &CaseRecord {
        &self.record
    }

    /// Consumes the runtime case and returns the persistent case metadata.
    pub(crate) fn into_record(self) -> CaseRecord {
        self.record
    }
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
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct CaseOutcome {
    /// The original benchmark metadata.
    pub(crate) case: CaseRecord,
    /// The wall-clock runtime measured by the parent process.
    #[serde(with = "duration_serde")]
    pub(crate) elapsed: Duration,
    /// The classified result category.
    pub(crate) category: OutcomeCategory,
    /// An optional detail string for failures and summaries.
    pub(crate) detail: Option<Box<str>>,
    /// Optional solver telemetry aggregated from periodic samples.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub(crate) telemetry: Option<CaseTelemetry>,
}

/// Saved solver telemetry for one executed benchmark case.
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct CaseTelemetry {
    /// Aggregate metrics derived from the raw periodic samples.
    pub(crate) summary: Summary,
    /// The raw periodic samples, kept only when the user requested `--save`.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub(crate) samples: Vec<Sample>,
}

use strum::VariantArray as _;

/// The top-level result category used in summaries and exit codes.
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize, strum::VariantArray)]
#[serde(rename_all = "snake_case")]
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
    pub(crate) const fn is_failure(self) -> bool {
        !matches!(self, Self::Pass | Self::NoOracle)
    }

    /// Returns the short uppercase label used in the terminal.
    pub(crate) const fn label(self) -> &'static str {
        match self {
            Self::Pass => "PASS",
            Self::NoOracle => "DONE",
            Self::WrongAnswer => "WRONG",
            Self::ParseError => "PARSE",
            Self::Timeout => "TIMEOUT",
            Self::Panic => "PANIC",
            Self::Killed => "KILLED",
            Self::HarnessError => "ERROR",
        }
    }

    /// Returns the terminal-styled label used in live and saved-run output.
    pub(crate) fn styled_label(self) -> StyledObject<&'static str> {
        match self {
            Self::WrongAnswer | Self::Killed | Self::HarnessError => {
                style(self.label()).red().bold()
            }
            Self::ParseError | Self::Timeout => style(self.label()).yellow().bold(),
            Self::Panic => style(self.label()).magenta().bold(),
            Self::Pass | Self::NoOracle => style(self.label()).green().bold(),
        }
    }

    /// The maximum length of the uppercase labels.
    pub(crate) const LABEL_WIDTH: usize = {
        let variants = Self::VARIANTS;
        let mut max = 0;
        let mut i = 0;

        while i < variants.len() {
            let len = variants[i].label().len();

            if len > max {
                max = len;
            }

            i += 1;
        }

        max
    };
}

/// Aggregate counters shown in the progress bar and final summary.
#[derive(Clone, Debug, Default, Eq, PartialEq, Serialize, Deserialize)]
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
#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) struct RunSummary {
    /// The file format version used for saved harness run results.
    #[serde(default = "RunSummary::format_version")]
    pub(crate) format_version: u32,
    /// The benchmark roots that were scanned for this run.
    pub(crate) roots: Box<[PathBuf]>,
    /// The number of workers that actually executed the run.
    pub(crate) jobs: usize,
    /// The configured per-case timeout.
    #[serde(with = "duration_serde")]
    pub(crate) timeout: Duration,
    /// The end-to-end wall-clock time for the full run.
    #[serde(with = "duration_serde")]
    pub(crate) total_elapsed: Duration,
    /// One saved outcome for each discovered case, sorted by comparison key.
    pub(crate) cases: Vec<CaseOutcome>,
    /// The final counters for all outcomes.
    pub(crate) stats: OutcomeStats,
}

impl RunSummary {
    /// The current on-disk file format version.
    pub(crate) const FORMAT_VERSION: u32 = 2;

    /// Returns the current on-disk file format version.
    pub(crate) const fn format_version() -> u32 {
        Self::FORMAT_VERSION
    }

    /// Validates that a deserialized summary uses a supported file format.
    pub(crate) fn validate(&self) -> Result<(), String> {
        if self.format_version == Self::FORMAT_VERSION {
            Ok(())
        } else {
            Err(format!(
                "unsupported saved result format version {} (expected {})",
                self.format_version,
                Self::FORMAT_VERSION
            ))
        }
    }
}

/// Serde helpers that encode durations as `{ secs, nanos }`.
mod duration_serde {
    use std::time::Duration;

    use serde::{Deserialize, Deserializer, Serialize, Serializer};

    /// Serializable duration payload used inside saved harness artifacts.
    #[derive(Deserialize, Serialize)]
    struct DurationRepr {
        /// Whole seconds since the start instant.
        secs: u64,
        /// Additional nanoseconds beyond `secs`.
        nanos: u32,
    }

    /// Serializes one duration into a stable structured representation.
    pub(crate) fn serialize<S>(duration: &Duration, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        DurationRepr {
            secs: duration.as_secs(),
            nanos: duration.subsec_nanos(),
        }
        .serialize(serializer)
    }

    /// Deserializes one duration from the saved structured representation.
    pub(crate) fn deserialize<'de, D>(deserializer: D) -> Result<Duration, D::Error>
    where
        D: Deserializer<'de>,
    {
        let repr = DurationRepr::deserialize(deserializer)?;
        Ok(Duration::new(repr.secs, repr.nanos))
    }
}
