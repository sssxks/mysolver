//! Small shared utility helpers for parsing, formatting, and process handling.

use std::process::ExitStatus;
use std::time::Duration;

/// Parses a user-provided timeout string such as `30s` or `250ms`.
pub(crate) fn parse_timeout(text: &str) -> Result<Duration, String> {
    humantime::parse_duration(text).map_err(|error| error.to_string())
}

/// Truncates long stderr and parser messages to a readable one-line detail.
pub(crate) fn trim_detail(text: &str) -> String {
    const LIMIT: usize = 160;
    let compact = text.replace('\n', " ");
    if compact.len() <= LIMIT {
        compact
    } else {
        format!("{}...", &compact[..LIMIT])
    }
}

/// Formats a duration using a short, benchmark-oriented representation.
pub(crate) fn format_compact_duration(duration: Duration) -> String {
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

/// Returns the terminating Unix signal for a child process, when available.
pub(crate) fn exit_signal(status: ExitStatus) -> Option<i32> {
    use std::os::unix::process::ExitStatusExt;

    status.signal()
}
