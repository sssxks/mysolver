//! Regression harness for running QF_UF benchmark fixtures against the solver.

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::fmt;
use std::fs::File;
use std::io::Read;
use std::num::NonZeroUsize;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{SystemTime, UNIX_EPOCH};

use lower::{Fuel, SatResult, Solver, SolverEvent};
use smtlib_lexer::parse_many;
use smtlib_syntax::{Command, ExpectedStatus};
use tar::Archive;
use zstd::stream::read::Decoder;

#[derive(Debug)]
struct FixtureError {
    path: Box<str>,
    message: Box<str>,
}

impl FixtureError {
    fn new(path: impl Into<Box<str>>, message: impl Into<Box<str>>) -> Self {
        Self {
            path: path.into(),
            message: message.into(),
        }
    }
}

impl fmt::Display for FixtureError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: {}", self.path, self.message)
    }
}

impl std::error::Error for FixtureError {}

/// In-memory copy of one SMT-LIB fixture loaded from the archive.
#[derive(Clone, Debug, Eq, PartialEq)]
struct ArchivedFixture {
    /// Relative path inside the fixture archive.
    path: Box<str>,
    /// Full SMT-LIB input for the fixture.
    input: Box<str>,
}

impl ArchivedFixture {
    /// Creates a fixture value owned by the random-subset sampler.
    fn new(path: impl Into<Box<str>>, input: impl Into<Box<str>>) -> Self {
        Self {
            path: path.into(),
            input: input.into(),
        }
    }
}

/// Configuration for a reproducible random archive subset.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct RandomSubsetConfig {
    /// Number of fixtures to keep in the subset.
    size: NonZeroUsize,
    /// Seed controlling fixture selection.
    seed: u64,
}

impl RandomSubsetConfig {
    /// Default subset size used when the caller does not override it.
    const DEFAULT_SIZE: usize = 32;

    /// Reads subset configuration from the environment for manual archive runs.
    fn from_env() -> Result<Self, FixtureError> {
        let size = std::env::var("QF_UF_RANDOM_SUBSET")
            .ok()
            .map(|value| {
                value.parse::<NonZeroUsize>().map_err(|error| {
                    FixtureError::new(
                        "QF_UF_RANDOM_SUBSET",
                        format!("invalid random subset size `{value}`: {error}"),
                    )
                })
            })
            .transpose()?
            .unwrap_or_else(|| match NonZeroUsize::new(Self::DEFAULT_SIZE) {
                Some(size) => size,
                None => unreachable!("default random subset size must be non-zero"),
            });
        let seed = std::env::var("QF_UF_RANDOM_SEED")
            .ok()
            .map(|value| {
                value.parse::<u64>().map_err(|error| {
                    FixtureError::new(
                        "QF_UF_RANDOM_SEED",
                        format!("invalid random subset seed `{value}`: {error}"),
                    )
                })
            })
            .transpose()?
            .unwrap_or_else(default_random_seed);
        Ok(Self { size, seed })
    }
}

/// Summary produced after selecting a random fixture subset.
#[derive(Debug, Eq, PartialEq)]
struct RandomSubsetSample {
    /// Total number of archive fixtures that matched the current filter.
    matching_fixture_count: usize,
    /// Fixtures chosen for this run.
    fixtures: Vec<ArchivedFixture>,
}

/// Heap item used to retain the lowest pseudo-random scores.
#[derive(Debug, Eq, PartialEq)]
struct RankedFixture {
    /// Score derived from the fixture path and configured seed.
    score: u64,
    /// Fixture selected into the current subset candidate set.
    fixture: ArchivedFixture,
}

impl Ord for RankedFixture {
    fn cmp(&self, other: &Self) -> Ordering {
        self.score
            .cmp(&other.score)
            .then_with(|| self.fixture.path.cmp(&other.fixture.path))
    }
}

impl PartialOrd for RankedFixture {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

fn qf_uf_archive_path() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../test/fixture/QF_UF.tar.zst")
        .canonicalize()
        .expect("QF_UF fixture archive exists")
}

/// Returns a pseudo-random but reproducible score for one fixture path.
fn fixture_random_score(seed: u64, path: &str) -> u64 {
    splitmix64(seed ^ fnv1a64(path.as_bytes()))
}

/// Computes a stable 64-bit FNV-1a hash for fixture names.
fn fnv1a64(bytes: &[u8]) -> u64 {
    const OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
    const PRIME: u64 = 0x0000_0100_0000_01b3;

    let mut hash = OFFSET_BASIS;
    for &byte in bytes {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(PRIME);
    }
    hash
}

/// Mixes a 64-bit value into a uniformly distributed pseudo-random score.
fn splitmix64(mut value: u64) -> u64 {
    value = value.wrapping_add(0x9e37_79b9_7f4a_7c15);
    value = (value ^ (value >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    value = (value ^ (value >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    value ^ (value >> 31)
}

/// Produces a seed for ad-hoc random subset runs.
fn default_random_seed() -> u64 {
    match SystemTime::now().duration_since(UNIX_EPOCH) {
        Ok(duration) => duration.as_nanos() as u64,
        Err(_) => 0,
    }
}

/// Keeps the `size` lowest-scoring fixtures from an iterator.
fn sample_archived_fixtures(
    fixtures: impl IntoIterator<Item = ArchivedFixture>,
    config: RandomSubsetConfig,
) -> RandomSubsetSample {
    let mut heap = BinaryHeap::new();
    let mut matching_fixture_count = 0usize;

    for fixture in fixtures {
        matching_fixture_count += 1;
        let ranked = RankedFixture {
            score: fixture_random_score(config.seed, &fixture.path),
            fixture,
        };
        if heap.len() < config.size.get() {
            heap.push(ranked);
            continue;
        }

        if heap.peek().is_some_and(|largest| ranked < *largest) {
            let _ = heap.pop();
            heap.push(ranked);
        }
    }

    let mut fixtures = heap
        .into_sorted_vec()
        .into_iter()
        .map(|ranked| ranked.fixture)
        .collect::<Vec<_>>();
    fixtures.sort_unstable_by(|left, right| left.path.cmp(&right.path));

    RandomSubsetSample {
        matching_fixture_count,
        fixtures,
    }
}

fn for_each_qf_uf_fixture(
    mut visit: impl FnMut(&str, &str) -> Result<(), FixtureError>,
) -> Result<usize, FixtureError> {
    let archive_path = qf_uf_archive_path();
    let archive_file = File::open(&archive_path).map_err(|error| {
        FixtureError::new(
            archive_path.display().to_string(),
            format!("failed to open fixture archive: {error}"),
        )
    })?;
    let decoder = Decoder::new(archive_file).map_err(|error| {
        FixtureError::new(
            archive_path.display().to_string(),
            format!("failed to create zstd decoder: {error}"),
        )
    })?;
    let mut archive = Archive::new(decoder);
    let mut count = 0usize;
    let filter = std::env::var("QF_UF_FILTER").ok();
    let limit = std::env::var("QF_UF_LIMIT")
        .ok()
        .and_then(|value| value.parse::<NonZeroUsize>().ok());

    let entries = archive.entries().map_err(|error| {
        FixtureError::new(
            archive_path.display().to_string(),
            format!("failed to enumerate tar entries: {error}"),
        )
    })?;
    for entry in entries {
        let mut entry = entry.map_err(|error| {
            FixtureError::new(
                archive_path.display().to_string(),
                format!("failed to read tar entry: {error}"),
            )
        })?;
        if !entry.header().entry_type().is_file() {
            continue;
        }

        let path = entry
            .path()
            .map_err(|error| {
                FixtureError::new(
                    archive_path.display().to_string(),
                    format!("failed to read tar entry path: {error}"),
                )
            })?
            .into_owned();
        let path_text = path.to_string_lossy().into_owned();
        if !path_text.ends_with(".smt2") {
            continue;
        }
        if let Some(filter) = filter.as_deref()
            && !path_text.contains(filter)
        {
            continue;
        }
        if limit.is_some_and(|limit| count >= limit.get()) {
            break;
        }

        let mut input = String::new();
        entry.read_to_string(&mut input).map_err(|error| {
            FixtureError::new(
                path_text.clone(),
                format!("failed to read fixture contents: {error}"),
            )
        })?;
        visit(&path_text, &input)?;
        count += 1;
    }

    Ok(count)
}

/// Loads a reproducible random subset of archive fixtures into memory.
fn sample_qf_uf_archive_fixtures(
    config: RandomSubsetConfig,
) -> Result<RandomSubsetSample, FixtureError> {
    let archive_path = qf_uf_archive_path();
    let archive_file = File::open(&archive_path).map_err(|error| {
        FixtureError::new(
            archive_path.display().to_string(),
            format!("failed to open fixture archive: {error}"),
        )
    })?;
    let decoder = Decoder::new(archive_file).map_err(|error| {
        FixtureError::new(
            archive_path.display().to_string(),
            format!("failed to create zstd decoder: {error}"),
        )
    })?;
    let mut archive = Archive::new(decoder);
    let filter = std::env::var("QF_UF_FILTER").ok();
    let entries = archive.entries().map_err(|error| {
        FixtureError::new(
            archive_path.display().to_string(),
            format!("failed to enumerate tar entries: {error}"),
        )
    })?;
    let mut fixtures = Vec::new();

    for entry in entries {
        let mut entry = entry.map_err(|error| {
            FixtureError::new(
                archive_path.display().to_string(),
                format!("failed to read tar entry: {error}"),
            )
        })?;
        if !entry.header().entry_type().is_file() {
            continue;
        }

        let path = entry
            .path()
            .map_err(|error| {
                FixtureError::new(
                    archive_path.display().to_string(),
                    format!("failed to read tar entry path: {error}"),
                )
            })?
            .into_owned();
        let path_text = path.to_string_lossy().into_owned();
        if !path_text.ends_with(".smt2") {
            continue;
        }
        if let Some(filter) = filter.as_deref()
            && !path_text.contains(filter)
        {
            continue;
        }

        let mut input = String::new();
        entry.read_to_string(&mut input).map_err(|error| {
            FixtureError::new(
                path_text.clone(),
                format!("failed to read fixture contents: {error}"),
            )
        })?;
        fixtures.push(ArchivedFixture::new(path_text, input));
    }

    Ok(sample_archived_fixtures(fixtures, config))
}

fn run_fixture(path: &str, input: &str, fuel_limit: Option<u64>) -> Result<usize, FixtureError> {
    let source = Arc::<str>::from(input);
    let exprs = parse_many(input)
        .map_err(|error| FixtureError::new(path, format!("parse error: {error}")))?;

    let mut solver = Solver::new();
    let mut fuel = fuel_limit.map(Fuel::new);
    let mut expected_status = None;
    let mut check_sat_count = 0usize;

    for expr in exprs {
        let command = Command::from_sexpr(&source, expr)
            .map_err(|error| FixtureError::new(path, format!("command error: {error}")))?;
        match command {
            Command::SetInfo(info) if info.expected_status.is_some() => {
                expected_status = info.expected_status.map(|status| match status {
                    ExpectedStatus::Sat => SatResult::Sat,
                    ExpectedStatus::Unsat => SatResult::Unsat,
                    ExpectedStatus::Unknown => SatResult::Unknown,
                });
            }
            other => {
                let event = match fuel.as_mut() {
                    Some(fuel) => solver.handle_command_with_budget(other, fuel),
                    None => solver.handle_command(other),
                }
                .map_err(|error| FixtureError::new(path, format!("solver error: {error}")))?;
                match event {
                    SolverEvent::None => {}
                    SolverEvent::Exit => break,
                    SolverEvent::CheckSat(actual) => {
                        check_sat_count += 1;
                        let expected = expected_status.ok_or_else(|| {
                            FixtureError::new(path, "check-sat without preceding :status")
                        })?;
                        if actual != expected {
                            return Err(FixtureError::new(
                                path,
                                format!(
                                    "check-sat #{check_sat_count} mismatch: expected {}, got {}",
                                    expected, actual
                                ),
                            ));
                        }
                    }
                }
            }
        }
    }

    if check_sat_count == 0 {
        return Err(FixtureError::new(
            path,
            "fixture does not contain check-sat",
        ));
    }

    Ok(check_sat_count)
}

#[test]
fn qf_uf_runner_tracks_status_per_check_sat() {
    let input = r#"
        (set-logic QF_UF)
        (set-info :status sat)
        (assert (= a b))
        (check-sat)
        (set-info :status unsat)
        (assert (distinct a b))
        (check-sat)
        (exit)
    "#;

    let checks = run_fixture("inline-qf-uf", input, None).expect("fixture succeeds");
    assert_eq!(checks, 2);
}

#[test]
fn qf_uf_runner_reports_interrupted_fixture() {
    let input = r#"
        (set-logic QF_UF)
        (set-info :status sat)
        (assert (= a b))
        (check-sat)
    "#;

    let error = run_fixture("inline-qf-uf", input, Some(0)).expect_err("fuel exhaustion fails");
    assert_eq!(
        error.to_string(),
        "inline-qf-uf: check-sat #1 mismatch: expected sat, got interrupted"
    );
}

#[test]
fn qf_uf_random_subset_sampling_is_seeded_and_bounded() {
    let fixtures = [
        ArchivedFixture::new("a.smt2", "(check-sat)"),
        ArchivedFixture::new("b.smt2", "(check-sat)"),
        ArchivedFixture::new("c.smt2", "(check-sat)"),
        ArchivedFixture::new("d.smt2", "(check-sat)"),
    ];
    let config = RandomSubsetConfig {
        size: match NonZeroUsize::new(2) {
            Some(size) => size,
            None => unreachable!("literal subset size must be non-zero"),
        },
        seed: 7,
    };

    let sample = sample_archived_fixtures(fixtures.iter().cloned(), config);
    let repeated_sample = sample_archived_fixtures(fixtures.iter().cloned(), config);

    assert_eq!(sample, repeated_sample);
    assert_eq!(sample.matching_fixture_count, fixtures.len());
    assert_eq!(sample.fixtures.len(), config.size.get());
}

#[test]
#[ignore = "slow full test"]
fn qf_uf_archive() {
    let fuel_limit = Some(100_000_000);
    let mut fixture_count = 0usize;
    let mut check_sat_count = 0usize;
    for_each_qf_uf_fixture(|path, input| {
        check_sat_count += run_fixture(path, input, fuel_limit)?;
        fixture_count += 1;
        if fixture_count.is_multiple_of(25) {
            eprintln!("validated {fixture_count} fixtures / {check_sat_count} check-sat calls");
        }
        Ok(())
    })
    .expect("archive fixtures succeed");
    assert!(fixture_count > 0, "QF_UF archive must contain fixtures");
    assert!(
        check_sat_count > 0,
        "QF_UF archive must contain check-sat commands"
    );
}

#[test]
fn qf_uf_archive_random_subset() {
    let config = RandomSubsetConfig::from_env().expect("random subset configuration is valid");
    let sample = sample_qf_uf_archive_fixtures(config).expect("archive fixtures can be sampled");
    let fuel_limit = Some(2_000_000);
    let mut check_sat_count = 0usize;

    eprintln!(
        "running {} sampled fixtures out of {} matching fixtures with seed {}",
        sample.fixtures.len(),
        sample.matching_fixture_count,
        config.seed
    );

    for fixture in &sample.fixtures {
        check_sat_count += run_fixture(&fixture.path, &fixture.input, fuel_limit)
            .expect("sampled fixture succeeds");
    }

    assert!(
        sample.matching_fixture_count > 0,
        "QF_UF archive must contain fixtures matching the current filter"
    );
    assert!(
        !sample.fixtures.is_empty(),
        "random subset must contain at least one fixture"
    );
    assert!(
        check_sat_count > 0,
        "sampled fixtures must contain check-sat commands"
    );
}
