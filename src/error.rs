//! Error type for numerical formatting.

use core::{fmt, num};

/// The error type returned when a checked integral type conversion fails.
pub struct TryFromIntError;

impl fmt::Display for TryFromIntError {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let msg = "out of range integral type conversion attempted";
        fmt::Display::fmt(msg, f)
    }
}

/// An error which can be returned when parsing an integer.
pub struct ParseIntError {
    pub kind: IntErrorKind,
}

/// Enum to store the various types of errors that can cause parsing an integer
/// to fail.
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum IntErrorKind {
    /// Value being parsed is empty.
    Empty,

    /// Contains an invalid digit in its context.
    InvalidDigit,

    /// Integer is too large to store in target integer type.
    PosOverflow,

    /// Integer is too small to store in target integer type.
    NegOverflow,

    /// Value was Zero
    Zero,

    #[doc(hidden)]
    Unknown,
}

impl ParseIntError {
    /// Outputs the detailed cause of parsing an integer failing.
    #[must_use]
    pub const fn kind(&self) -> &IntErrorKind {
        &self.kind
    }
}

impl fmt::Display for ParseIntError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let description = match self.kind {
            IntErrorKind::Empty => "cannot parse integer from empty string",
            IntErrorKind::InvalidDigit => "invalid digit found in string",
            IntErrorKind::PosOverflow => "number too large to fit in target type",
            IntErrorKind::NegOverflow => "number too small to fit in target type",
            IntErrorKind::Zero => "number would be zero for non-zero type",
            IntErrorKind::Unknown => "unknown, internal error",
        };
        description.fmt(f)
    }
}

impl From<num::ParseIntError> for ParseIntError {
    #[inline]
    fn from(other: num::ParseIntError) -> ParseIntError {
        let kind = match *other.kind() {
            num::IntErrorKind::Empty => IntErrorKind::Empty,
            num::IntErrorKind::InvalidDigit => IntErrorKind::InvalidDigit,
            num::IntErrorKind::PosOverflow => IntErrorKind::PosOverflow,
            num::IntErrorKind::NegOverflow => IntErrorKind::NegOverflow,
            num::IntErrorKind::Zero => IntErrorKind::Zero,
            _ => IntErrorKind::Unknown,
        };
        ParseIntError {
            kind,
        }
    }
}
