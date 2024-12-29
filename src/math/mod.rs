//! Arithmetic utilities.
//!
//! This is used for logic to create larger type sizes, allowing
//! multiplication and more from smaller components, while also
//! making testing easier (so the data can be tested from smaller
//! components to known reference values).

// NOTE: This mostly exists for testing and is exposed for that reason.
#![doc(hidden)]

pub mod add;
pub mod bigint;
pub mod div;
pub mod mul;
pub mod rotate;
pub mod shift;
pub mod sub;
