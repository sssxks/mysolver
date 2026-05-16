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

/// Truncates a rendered case path by keeping the first 10 and last 25 characters.
pub(crate) fn truncate_display_path(display_path: &str) -> String {
    const DISPLAY_PATH_HEAD_CHARS: usize = 10;
    const DISPLAY_PATH_TAIL_CHARS: usize = 25;

    let total_chars = display_path.chars().count();
    if total_chars <= DISPLAY_PATH_HEAD_CHARS + DISPLAY_PATH_TAIL_CHARS {
        return display_path.to_owned();
    }

    let head_end = char_boundary_at(display_path, DISPLAY_PATH_HEAD_CHARS);
    let tail_start = char_boundary_at(display_path, total_chars - DISPLAY_PATH_TAIL_CHARS);
    format!(
        "{}..{}",
        &display_path[..head_end],
        &display_path[tail_start..]
    )
}

/// Returns the byte boundary at the requested character index.
fn char_boundary_at(text: &str, char_index: usize) -> usize {
    text.char_indices()
        .nth(char_index)
        .map_or(text.len(), |(index, _)| index)
}

/// Returns the terminating Unix signal for a child process, when available.
pub(crate) fn exit_signal(status: ExitStatus) -> Option<i32> {
    use std::os::unix::process::ExitStatusExt;

    status.signal()
}
