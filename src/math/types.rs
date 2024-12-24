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

use core::mem;

// NOTE: Since we're using 128-bits under the hood, we just assume every
// architecture can use 64-bit limbs, which is true of most modern systems.
// This might not be true in which case we can address this at that time.
pub type ULimb = u64;
pub type ILimb = i64;
pub type UWide = u128;
pub type IWide = i128;

// The number of limbs in the integer for a 256-bit integer.
pub const LIMBS: usize = (256 / ULimb::BITS) as usize;

/// Flatten two 128-bit integers as bytes to flat, 32 bytes.
///
/// We keep this as a standalone function since Rust can sometimes
/// vectorize this in a way using purely safe Rust cannot, which
/// improves performance while ensuring we are very careful.
/// These are guaranteed to be plain old [`data`] with a fixed size
/// alignment, and padding.
///
/// [`data`]: https://rust-lang.github.io/unsafe-code-guidelines/layout/scalars.html#fixed-width-integer-types
#[inline(always)]
pub const fn to_flat_bytes(x: [u8; 16], y: [u8; 16]) -> [u8; 32] {
    // SAFETY: plain old data
    unsafe { mem::transmute::<[[u8; 16]; 2], [u8; 32]>([x, y]) }
}

/// Flatten a flat, 32 byte integer to two 128-bit integers as bytes.
///
/// We keep this as a standalone function since Rust can sometimes
/// vectorize this in a way using purely safe Rust cannot, which
/// improves performance while ensuring we are very careful.
/// These are guaranteed to be plain old [`data`] with a fixed size
/// alignment, and padding.
///
/// [`data`]: https://rust-lang.github.io/unsafe-code-guidelines/layout/scalars.html#fixed-width-integer-types
#[inline(always)]
pub const fn from_flat_bytes(bytes: [u8; 32]) -> ([u8; 16], [u8; 16]) {
    // SAFETY: plain old data
    let r = unsafe { mem::transmute::<[u8; 32], [[u8; 16]; 2]>(bytes) };
    (r[0], r[1])
}

/// Convert an array of limbs to the flat bytes.
///
/// We keep this as a standalone function since Rust can sometimes
/// vectorize this in a way using purely safe Rust cannot, which
/// improves performance while ensuring we are very careful.
/// These are guaranteed to be plain old [`data`] with a fixed size
/// alignment, and padding.
///
/// [`data`]: https://rust-lang.github.io/unsafe-code-guidelines/layout/scalars.html#fixed-width-integer-types
#[inline(always)]
pub const fn from_limbs(limbs: [ULimb; LIMBS]) -> [u8; 32] {
    // SAFETY: This is plain old data
    unsafe { mem::transmute::<[ULimb; LIMBS], [u8; 32]>(limbs) }
}

/// Convert flat bytes to an array of limbs.
///
/// We keep this as a standalone function since Rust can sometimes
/// vectorize this in a way using purely safe Rust cannot, which
/// improves performance while ensuring we are very careful.
/// These are guaranteed to be plain old [`data`] with a fixed size
/// alignment, and padding.
///
/// [`data`]: https://rust-lang.github.io/unsafe-code-guidelines/layout/scalars.html#fixed-width-integer-types
#[inline(always)]
pub const fn to_limbs(bytes: [u8; 32]) -> [ULimb; LIMBS] {
    // SAFETY: This is plain old data
    unsafe { mem::transmute(bytes) }
}

/// Swap the order of limbs, useful for re-arranging for BE/LE order.
#[inline(always)]
pub const fn swap_limbs(limbs: [ULimb; LIMBS]) -> [ULimb; LIMBS] {
    let mut res = [0; LIMBS];
    let mut i = 0;
    while i < LIMBS {
        res[i] = limbs[LIMBS - i - 1];
        i += 1;
    }
    res
}
