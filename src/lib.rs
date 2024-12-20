//! Optimized implementations of 256-bit signed and unsigned integers.
//!
//! This contains a fixed-width, performant implementation for 256-bit
//! signed and unsigned integers. This has significantly faster performance
//! for basic math operations than comparable fixed-width integer types,
//! since it can use optimizations from 128-bit integers on 64-bit
//! architectures.

#![allow(unused_unsafe)]
#![cfg_attr(feature = "lint", warn(unsafe_op_in_unsafe_fn))]
#![cfg_attr(not(feature = "std"), no_std)]
#![deny(
    clippy::doc_markdown,
    clippy::unnecessary_safety_comment,
    clippy::semicolon_if_nothing_returned,
    clippy::unwrap_used,
    clippy::as_underscore,
    clippy::doc_markdown
)]

mod error;
// exposed only for testing
pub mod math;

mod ints;
mod numtypes;

pub use error::{IntErrorKind, ParseIntError, TryFromIntError};
pub use ints::i256::i256;
pub use ints::u256::u256;
