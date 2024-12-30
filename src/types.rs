//!  Type for a single limb of the big integer.
//!
//!  A limb is analogous to a digit in base10, except, it stores 32-bit
//!  or 64-bit numbers instead.
//!
//!  This should be all-known 64-bit [`platforms`] supported by Rust.
//!
//!  Platforms where native 128-bit multiplication is explicitly supported:
//!      - `x86_64` (Supported via `MUL`).
//!      - `mips64` (Supported via `DMULTU`, which `HI` and `LO` can be
//!        read-from).
//!
//!  Platforms where native 64-bit multiplication is supported and
//!  you can extract hi-lo for 64-bit multiplications.
//!      `aarch64` (Requires `UMULH` and `MUL` to capture high and low bits).
//!      `powerpc64` (Requires `MULHDU` and `MULLD` to capture high and low
//! bits).
//!
//!  Platforms where native 128-bit multiplication is not supported,
//!  requiring software emulation.
//!      `sparc64` (`UMUL` only supported double-word arguments).
//!
//! [`platforms`]: https://forge.rust-lang.org/platform-support.html

// NOTE: Since we're using 128-bits under the hood, we just assume every
// architecture can use 64-bit limbs, which is true of most modern systems.
// This might not be true in which case we can address this at that time.

/// The unsigned type used as a native "limb".
#[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
pub type ULimb = u64;

/// The unsigned type used as a native "limb".
#[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
pub type ULimb = u32;

/// The same sized type of the limb as a signed integer.
#[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
pub type ILimb = i64;

/// The same sized type of the limb as a signed integer.
#[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
pub type ILimb = i32;

/// An unsigned type double the width of the limb.
#[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
pub type UWide = u128;

/// An unsigned type double the width of the limb.
#[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
pub type UWide = u64;

/// A signed type double the width of the limb.
#[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
pub type IWide = i128;

/// A signed type double the width of the limb.
#[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
pub type IWide = i64;
