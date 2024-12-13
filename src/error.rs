//! Error type for numerical formatting.

use core::fmt;

/// The error type returned when a checked integral type conversion fails.
pub struct TryFromIntError;

impl fmt::Display for TryFromIntError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = "out of range integral type conversion attempted";
        fmt::Display::fmt(msg, f)
    }
}
