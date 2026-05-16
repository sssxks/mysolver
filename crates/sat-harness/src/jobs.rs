//! Worker-count selection for parent-process scheduling.

use std::collections::HashSet;
use std::fs;
use std::io;
use std::num::NonZeroUsize;
use std::path::PathBuf;

/// Returns the default worker count for parent-process scheduling.
///
/// The harness prefers the number of physical CPU cores available to the
/// current process so that SMT siblings do not inflate the worker count.
/// When the Linux topology data cannot be read, it falls back to the standard
/// library's logical parallelism hint.
pub(crate) fn default_jobs() -> NonZeroUsize {
    physical_core_count()
        .unwrap_or_else(|| std::thread::available_parallelism().unwrap_or(NonZeroUsize::MIN))
}

/// Returns the number of physical CPU cores available to the current process.
///
/// The count is derived from `/proc/self/status` and Linux CPU topology files,
/// which lets the harness respect CPU affinity and cpuset constraints instead
/// of blindly using the machine-wide physical core count.
fn physical_core_count() -> Option<NonZeroUsize> {
    let allowed_cpus = allowed_cpu_indices().ok()?;
    let mut physical_cores = HashSet::with_capacity(allowed_cpus.len());

    for cpu_index in allowed_cpus {
        let physical_package_id = read_topology_id(cpu_index, "physical_package_id").ok()?;
        let core_id = read_topology_id(cpu_index, "core_id").ok()?;
        physical_cores.insert((physical_package_id, core_id));
    }

    NonZeroUsize::new(physical_cores.len())
}

/// Returns the logical CPU indices the current process may run on.
fn allowed_cpu_indices() -> io::Result<Box<[usize]>> {
    let status = fs::read_to_string("/proc/self/status")?;
    let allowed = status
        .lines()
        .find_map(|line| line.strip_prefix("Cpus_allowed_list:"))
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidData, "missing Cpus_allowed_list"))?;
    parse_cpu_list(allowed.trim())
}

/// Parses one Linux CPU-list string such as `0-3,8-11`.
fn parse_cpu_list(text: &str) -> io::Result<Box<[usize]>> {
    let mut cpus = Vec::new();

    for raw_segment in text.split(',') {
        let segment = raw_segment.trim();
        if segment.is_empty() {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "empty CPU-list segment",
            ));
        }

        let Some((start, end)) = segment.split_once('-') else {
            cpus.push(parse_cpu_index(segment)?);
            continue;
        };

        let start = parse_cpu_index(start.trim())?;
        let end = parse_cpu_index(end.trim())?;
        if start > end {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "descending CPU range",
            ));
        }

        cpus.extend(start..=end);
    }

    Ok(cpus.into_boxed_slice())
}

/// Parses one CPU index from a Linux affinity list.
fn parse_cpu_index(text: &str) -> io::Result<usize> {
    text.parse::<usize>().map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("invalid CPU index `{text}`: {error}"),
        )
    })
}

/// Reads one numeric CPU topology attribute from Linux sysfs.
fn read_topology_id(cpu_index: usize, name: &str) -> io::Result<u32> {
    let path = PathBuf::from(format!(
        "/sys/devices/system/cpu/cpu{cpu_index}/topology/{name}"
    ));
    let raw = fs::read_to_string(&path)?;
    raw.trim().parse::<u32>().map_err(|error| {
        io::Error::new(
            io::ErrorKind::InvalidData,
            format!("invalid topology value in {}: {error}", path.display()),
        )
    })
}

#[cfg(test)]
mod tests {
    use std::io;

    use super::parse_cpu_list;

    /// Ensures Linux CPU lists expand inclusive ranges correctly.
    #[test]
    fn parse_cpu_list_expands_ranges() {
        let parsed = parse_cpu_list("0-2,5,8-9").expect("parse CPU list");
        assert_eq!(&*parsed, &[0, 1, 2, 5, 8, 9]);
    }

    /// Rejects invalid descending CPU ranges instead of silently swapping them.
    #[test]
    fn parse_cpu_list_rejects_descending_ranges() {
        let error = parse_cpu_list("3-1").expect_err("descending range should fail");
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    }

    /// Rejects malformed CPU indices so affinity parsing cannot undercount cores.
    #[test]
    fn parse_cpu_list_rejects_invalid_indices() {
        let error = parse_cpu_list("0,a").expect_err("invalid CPU index should fail");
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
    }
}
