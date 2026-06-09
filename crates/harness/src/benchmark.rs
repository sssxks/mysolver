//! Repeated single-case benchmarking.
//!
//! The command measures the same subprocess-isolated path as the main harness,
//! but fixes discovery to one case and executes it repeatedly.
//!
//! | Operation | Frequency | Complexity | Data structure | Forbidden Impl |
//! | - | - | - | - | - |
//! | Record one run | Once per run | O(1) | `Vec<CaseOutcome>` | Re-discover case each iteration |
//! | Compute distribution | Once after all runs | O(n log n) | Sorted `Vec<Duration>` | Re-scan outcomes for every percentile |

use std::env;
use std::time::{Duration, Instant};

use console::style;
use indicatif::{HumanCount, HumanDuration};

use crate::cli::BenchArgs;
use crate::discover::discover_cases;
use crate::model::{CaseOutcome, OutcomeCategory};
use crate::parent::run_case_subprocess;
use crate::render::format_outcome;
use crate::util::format_compact_duration;

/// Runs one case repeatedly and prints an elapsed-time distribution.
pub(crate) fn run_benchmark(args: BenchArgs) -> Result<BenchmarkSummary, String> {
    let cases = discover_cases(std::slice::from_ref(&args.case))?;
    let [case] = cases.as_slice() else {
        return Err(format!(
            "benchmark target must resolve to exactly one supported case, found {}",
            cases.len()
        ));
    };
    let current_exe = env::current_exe()
        .map_err(|error| format!("failed to locate current executable: {error}"))?;

    eprintln!(
        "{} {} for {} measured runs (timeout {})",
        style("benchmark").cyan().bold(),
        case.absolute_path().display(),
        HumanCount(args.iterations.get() as u64),
        HumanDuration(args.timeout),
    );
    if args.warmup > 0 {
        eprintln!(
            "{} {} unmeasured runs",
            style("warmup").cyan().bold(),
            HumanCount(args.warmup as u64),
        );
    }

    for index in 0..args.warmup {
        let outcome = run_case_subprocess(&current_exe, case.clone(), args.timeout);
        if outcome.category.is_failure() {
            eprintln!(
                "{} {}/{} failed before measurement:",
                style("warmup").red().bold(),
                HumanCount((index + 1) as u64),
                HumanCount(args.warmup as u64),
            );
            eprintln!("{}", format_outcome(&outcome));
            return Ok(BenchmarkSummary {
                measured: Vec::new(),
                distribution: None,
                failures: 1,
                total_elapsed: Duration::ZERO,
            });
        }
    }

    let started = Instant::now();
    let mut measured = Vec::with_capacity(args.iterations.get());
    for index in 0..args.iterations.get() {
        let outcome = run_case_subprocess(&current_exe, case.clone(), args.timeout);
        eprintln!(
            "{} {}/{} {}",
            style("run").cyan().bold(),
            HumanCount((index + 1) as u64),
            HumanCount(args.iterations.get() as u64),
            format_outcome(&outcome).trim_start(),
        );
        measured.push(outcome);
    }
    let total_elapsed = started.elapsed();

    let summary = BenchmarkSummary::new(measured, total_elapsed);
    print_summary(&summary);
    Ok(summary)
}

/// Aggregate result for a repeated single-case benchmark.
#[derive(Debug)]
pub(crate) struct BenchmarkSummary {
    /// All measured subprocess runs.
    measured: Vec<CaseOutcome>,
    /// Distribution over successful measured runs.
    distribution: Option<ElapsedDistribution>,
    /// The number of measured runs that failed classification.
    failures: usize,
    /// Total wall-clock time spent in measured runs.
    total_elapsed: Duration,
}

impl BenchmarkSummary {
    /// Builds a summary from measured subprocess outcomes.
    fn new(measured: Vec<CaseOutcome>, total_elapsed: Duration) -> Self {
        let failures = measured
            .iter()
            .filter(|outcome| outcome.category.is_failure())
            .count();
        let mut timings = measured
            .iter()
            .filter(|outcome| is_measured_category(outcome.category))
            .map(|outcome| outcome.elapsed)
            .collect::<Vec<_>>();
        let distribution = ElapsedDistribution::new(&mut timings);

        Self {
            measured,
            distribution,
            failures,
            total_elapsed,
        }
    }

    /// Returns `true` when at least one run failed.
    pub(crate) const fn has_failures(&self) -> bool {
        self.failures > 0
    }
}

/// Returns whether one outcome contributes to the timing distribution.
const fn is_measured_category(category: OutcomeCategory) -> bool {
    matches!(category, OutcomeCategory::Pass | OutcomeCategory::NoOracle)
}

/// Percentile distribution for successful measured elapsed times.
#[derive(Copy, Clone, Debug, Eq, PartialEq)]
struct ElapsedDistribution {
    /// Number of successful measured samples.
    samples: usize,
    /// Fastest successful run.
    min: Duration,
    /// 25th percentile using nearest-rank indexing.
    p25: Duration,
    /// Median using nearest-rank indexing.
    median: Duration,
    /// 75th percentile using nearest-rank indexing.
    p75: Duration,
    /// 90th percentile using nearest-rank indexing.
    p90: Duration,
    /// 99th percentile using nearest-rank indexing.
    p99: Duration,
    /// Slowest successful run.
    max: Duration,
    /// Arithmetic mean over all successful runs.
    mean: Duration,
}

impl ElapsedDistribution {
    /// Builds a distribution from an unsorted timing buffer.
    fn new(timings: &mut [Duration]) -> Option<Self> {
        if timings.is_empty() {
            return None;
        }

        timings.sort_unstable();
        let samples = timings.len();
        let total_nanos = timings.iter().map(Duration::as_nanos).sum::<u128>();
        let mean = duration_from_nanos(total_nanos / samples as u128);

        Some(Self {
            samples,
            min: timings[0],
            p25: percentile(timings, 25),
            median: percentile(timings, 50),
            p75: percentile(timings, 75),
            p90: percentile(timings, 90),
            p99: percentile(timings, 99),
            max: timings[samples - 1],
            mean,
        })
    }
}

/// Returns the nearest-rank percentile from sorted timings.
fn percentile(sorted: &[Duration], percentile: u32) -> Duration {
    debug_assert!(!sorted.is_empty());
    debug_assert!(percentile <= 100);
    let index = (sorted.len() * percentile as usize).div_ceil(100);
    sorted[index.saturating_sub(1)]
}

/// Converts an integer nanosecond count into `Duration`.
fn duration_from_nanos(nanos: u128) -> Duration {
    let secs = nanos / 1_000_000_000;
    let subsec_nanos = nanos % 1_000_000_000;
    Duration::new(secs as u64, subsec_nanos as u32)
}

/// Prints the final benchmark summary.
fn print_summary(summary: &BenchmarkSummary) {
    let measured = summary.measured.len();
    let successful = measured.saturating_sub(summary.failures);
    let throughput = if summary.total_elapsed.is_zero() {
        0.0
    } else {
        measured as f64 / summary.total_elapsed.as_secs_f64()
    };

    eprintln!();
    eprintln!(
        "{} measured {} | successful {} | failures {} | total {} | throughput {:.1} runs/s",
        style("distribution").cyan().bold(),
        HumanCount(measured as u64),
        HumanCount(successful as u64),
        HumanCount(summary.failures as u64),
        format_compact_duration(summary.total_elapsed),
        throughput,
    );

    let Some(distribution) = summary.distribution else {
        eprintln!("no successful measured runs");
        return;
    };

    eprintln!(
        "samples {} | min {} | p25 {} | median {} | p75 {} | p90 {} | p99 {} | max {} | mean {}",
        HumanCount(distribution.samples as u64),
        format_compact_duration(distribution.min),
        format_compact_duration(distribution.p25),
        format_compact_duration(distribution.median),
        format_compact_duration(distribution.p75),
        format_compact_duration(distribution.p90),
        format_compact_duration(distribution.p99),
        format_compact_duration(distribution.max),
        format_compact_duration(distribution.mean),
    );
}

#[cfg(test)]
mod tests {
    use std::time::Duration;

    use super::{ElapsedDistribution, duration_from_nanos, percentile};

    /// Ensures percentile lookup uses nearest-rank indexing.
    #[test]
    fn percentile_uses_nearest_rank() {
        let timings = [
            Duration::from_millis(1),
            Duration::from_millis(2),
            Duration::from_millis(3),
            Duration::from_millis(4),
        ];

        assert_eq!(percentile(&timings, 25), Duration::from_millis(1));
        assert_eq!(percentile(&timings, 50), Duration::from_millis(2));
        assert_eq!(percentile(&timings, 90), Duration::from_millis(4));
    }

    /// Ensures distribution construction sorts timings and computes mean.
    #[test]
    fn distribution_sorts_and_summarizes_timings() {
        let mut timings = [
            Duration::from_millis(4),
            Duration::from_millis(1),
            Duration::from_millis(3),
            Duration::from_millis(2),
        ];

        let distribution = ElapsedDistribution::new(&mut timings).expect("distribution");

        assert_eq!(distribution.samples, 4);
        assert_eq!(distribution.min, Duration::from_millis(1));
        assert_eq!(distribution.median, Duration::from_millis(2));
        assert_eq!(distribution.max, Duration::from_millis(4));
        assert_eq!(
            distribution.mean,
            Duration::from_millis(2) + Duration::from_micros(500)
        );
    }

    /// Ensures nanosecond conversion preserves subsecond precision.
    #[test]
    fn duration_from_nanos_keeps_remainder() {
        assert_eq!(
            duration_from_nanos(1_234_567_890),
            Duration::new(1, 234_567_890),
        );
    }
}
