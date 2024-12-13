//! TODO Document

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

pub mod error;

mod math;
mod numtypes;
mod ints;

// TODO: Add intrinsics if we can here
// This might help a lot on x86 and arm64

pub use ints::i256::i256;
pub use ints::u256::u256;
