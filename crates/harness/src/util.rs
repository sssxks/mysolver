//! Small shared utility helpers for parsing, formatting, and process handling.

use std::time::Duration;

/// Formats a duration using a short, benchmark-oriented representation.
pub(crate) fn format_duration(duration: Duration) -> String {
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
