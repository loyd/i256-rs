//! An signed 256-bit integer type.
//!
//! This aims to have feature parity with Rust's signed
//! integer types, such as [i32][core::i32]. The documentation
//! is based off of [i32][core::i32] for each method/member.
//!
//! Rust's signed integers are guaranteed to be [`two's complement`],
//! so we guarantee the same representation internally.
//!
//! [`two's complement`]: https://en.wikipedia.org/wiki/Two%27s_complement
//!
//! A large portion of the implementation for helper functions
//! are based off of the Rust core implementation, such as for
//! [`checked_pow`][i128::checked_pow], [`isqrt`][i128::isqrt],
//! and more. Any non-performance critical functions, or those
//! crucial to parsing or serialization ([`add`][`i256::add`],
//! [`mul`][`i256::mul`], [`div`][`i256::div`], and
//! [`sub`][`i256::sub`]), as well as their `wrapping_*`,
//! `checked_*`, `overflowing_*` and `*_wide` variants are
//! likely based on the core implementations.

use core::ops::*;

use super::int_macros::*;
use super::shared_macros::*;
use crate::math;
use crate::parse::from_str_radix_define;
use crate::write::to_str_radix_define;
use crate::{u256, ILimb, IWide, TryFromIntError, ULimb, UWide};

int_define!(i256, 256, signed);

impl i256 {
    /// The smallest value that can be represented by this integer type.
    ///
    /// See [`i128::MIN`].
    pub const MIN: Self = Self::new(0, i128::MIN);

    /// The largest value that can be represented by this integer type
    /// (2<sup>256</sup> - 1).
    ///
    /// See [`i128::MAX`].
    pub const MAX: Self = Self::new(u128::MAX, i128::MAX);

    /// The size of this integer type in bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use i256::i256;
    /// assert_eq!(i256::BITS, 256);
    /// ```
    ///
    /// See [`i128::BITS`].
    pub const BITS: u32 = 256;

    /// The number of decimal digits for the largest magnitude value.
    pub const MAX_DIGITS: usize = 77;

    int_impl_define!(u256, 256, u128, i128, signed);

    /// Shifts the bits to the left by a specified amount, `n`,
    /// wrapping the truncated bits to the end of the resulting integer.
    ///
    /// Please note this isn't the same operation as the `<<` shifting operator!
    ///
    /// See [`i128::rotate_left`].
    #[inline(always)]
    pub const fn rotate_left(self, n: u32) -> Self {
        let (lo, hi) = math::rotate_left_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Shifts the bits to the right by a specified amount, `n`,
    /// wrapping the truncated bits to the beginning of the resulting
    /// integer.
    ///
    /// Please note this isn't the same operation as the `>>` shifting operator!
    ///
    /// See [`i128::rotate_right`].
    #[inline(always)]
    pub const fn rotate_right(self, n: u32) -> Self {
        let (lo, hi) = math::rotate_right_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Reverses the byte order of the integer.
    ///
    /// See [`i128::swap_bytes`].
    #[inline(always)]
    pub const fn swap_bytes(self) -> Self {
        let (lo, hi) = math::swap_bytes_i128(self.low(), self.high());
        Self::new(lo, hi)
    }

    /// Reverses the order of bits in the integer. The least significant
    /// bit becomes the most significant bit, second least-significant bit
    /// becomes second most-significant bit, etc.
    ///
    /// See [`i128::reverse_bits`].
    #[inline(always)]
    pub const fn reverse_bits(self) -> Self {
        let (lo, hi) = math::reverse_bits_i128(self.low(), self.high());
        Self::new(lo, hi)
    }

    /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at
    /// the boundary of the type.
    ///
    /// See [`i128::wrapping_add`].
    #[inline(always)]
    pub const fn wrapping_add(self, rhs: Self) -> Self {
        let (lo, hi) = math::wrapping_add_i128(self.low(), self.high(), rhs.low(), rhs.high());
        i256::new(lo, hi)
    }

    /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around
    /// at the boundary of the type.
    ///
    /// See [`i128::wrapping_sub`].
    #[inline(always)]
    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        let (lo, hi) = math::wrapping_sub_i128(self.low(), self.high(), rhs.low(), rhs.high());
        i256::new(lo, hi)
    }

    /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping
    /// around at the boundary of the type.
    ///
    /// See [`i128::wrapping_mul`].
    #[inline(always)]
    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        let (lo, hi) = math::wrapping_mul_i128(self.low(), self.high(), rhs.low(), rhs.high());
        i256::new(lo, hi)
    }

    /// Div/Rem operation on a 256-bit integer.
    ///
    /// This allows storing of both the quotient and remainder without
    /// making repeated calls.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    #[inline]
    pub fn wrapping_div_rem(self, n: Self) -> (Self, Self) {
        // NOTE: Our algorithm assumes little-endian order, which we might not have.
        // So, we transmute to LE order prior to the call.
        // Do division as positive numbers, and if `lhs.is_sign_negative() ^
        // rhs.is_sign_negative()`, then we can inver the sign
        let x = self.wrapping_abs().as_u256().to_le_limbs();
        let y = n.wrapping_abs().as_u256().to_le_limbs();

        // get our unsigned division product
        let (div, rem) = math::div_rem_full(&x, &y);
        let mut div = u256::from_le_limbs(div).as_i256();
        let mut rem = u256::from_le_limbs(rem).as_i256();

        // convert to our correct signs, get the product
        if self.is_negative() != n.is_negative() {
            div = div.wrapping_neg();
        }
        if self.is_negative() {
            rem = rem.wrapping_neg();
        }

        (div, rem)
    }

    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`, where `mask`
    /// removes any high-order bits of `rhs` that would cause the shift to
    /// exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-left; the RHS of a wrapping
    /// shift-left is restricted to the range of the type, rather than the
    /// bits shifted out of the LHS being returned to the other end.
    /// The primitive integer types all implement a
    /// [`rotate_left`](Self::rotate_left) function, which may be what you
    /// want instead.
    ///
    /// See [`i128::wrapping_shl`].
    #[inline(always)]
    pub const fn wrapping_shl(self, rhs: u32) -> Self {
        let (lo, hi) = math::shl_i128(self.low(), self.high(), rhs % Self::BITS);
        Self::new(lo, hi)
    }

    /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`, where `mask`
    /// removes any high-order bits of `rhs` that would cause the shift to
    /// exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-right; the RHS of a
    /// wrapping shift-right is restricted to the range of the type, rather
    /// than the bits shifted out of the LHS being returned to the other
    /// end. The primitive integer types all implement a
    /// [`rotate_right`](Self::rotate_right) function, which may be what you
    /// want instead.
    ///
    /// See [`i128::wrapping_shr`].
    #[inline(always)]
    pub const fn wrapping_shr(self, rhs: u32) -> Self {
        let (lo, hi) = math::shr_i128(self.low(), self.high(), rhs % 256);
        Self::new(lo, hi)
    }

    /// Calculates `self` + `rhs`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would have
    /// occurred then the wrapped value is returned.
    ///
    /// See [`i128::overflowing_add`].
    #[inline(always)]
    pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) =
            math::overflowing_add_i128(self.low(), self.high(), rhs.low(), rhs.high());
        (Self::new(lo, hi), overflowed)
    }

    /// Calculates `self` - `rhs`.
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    ///
    /// See [`i128::overflowing_sub`].
    #[inline(always)]
    pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) =
            math::overflowing_sub_i128(self.low(), self.high(), rhs.low(), rhs.high());
        (Self::new(lo, hi), overflowed)
    }

    /// Calculates the multiplication of `self` and `rhs`.
    ///
    /// Returns a tuple of the multiplication along with a boolean
    /// indicating whether an arithmetic overflow would occur. If an
    /// overflow would have occurred then the wrapped value is returned.
    ///
    /// See [`i128::overflowing_mul`].
    #[inline(always)]
    pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) =
            math::overflowing_mul_i128(self.low(), self.high(), rhs.low(), rhs.high());
        (i256::new(lo, hi), overflowed)
    }

    /// Returns `true` if `self` is positive and `false` if the number is zero
    /// or negative.
    ///
    /// See [`i128::is_positive`].
    #[inline(always)]
    pub const fn is_positive(self) -> bool {
        // NOTE: Because this is 2's complement, we can optimize like this.
        self.high() > 0 || (self.high() == 0 && self.low() > 0)
    }

    /// Returns `true` if `self` is negative and `false` if the number is zero
    /// or positive.
    ///
    /// See [`i128::is_negative`].
    #[inline(always)]
    pub const fn is_negative(self) -> bool {
        // NOTE: Because this is 2's complement, we can optimize like this.
        self.high() < 0
    }

    from_str_radix_define!(true);
    to_str_radix_define!(true);
}

// NOTE: Validation of the bit patterns for types can be done as:
//
// ```python
// from bitstring import BitArray
//
// def sbin(n, l, be='big'):
//     bits = BitArray(n.to_bytes(l, signed=True, byteorder=be)).bin
//     return '0b' + bits
//
// def ubin(n, l, be='big'):
//     bits = BitArray(n.to_bytes(l, signed=False, byteorder=be)).bin
//     return '0b' + bits
// ```
//
// These are output in big-endian order. Great testing includes
// unique bit patterns, like `ubin(0x123579, 4)`, which has a unique
// bit order (`0b00000000000100100011010101111001`), which we can
// check for truncation to `u16` from `u32`, etc., as well as conversions
// to signed and conversions to `i16` from `i32`. Casting to `u16` leaves
// `0x3579`, as does `i32` to `i16`. Similarly, `-0x123579i32 as i16` is
// then truncated to `-0x3579`.
//
// Meanwhile, `sbin(-0x123579`, 4) == 0b11111111111011011100101010000111`.
//
// **Big:**
// - +0x123579i32: 0b00000000 00010010 00110101 01111001
// - -0x123579i32: 0b11111111 11101101 11001010 10000111
//
// - +0x3579i16:   0b                  00110101 01111001
// - -0x3579i16:   0b                  11001010 10000111
//
// **Little:**
// - +0x123579i32: 0b01111001 00110101 00010010 00000000
// - -0x123579i32: 0b10000111 11001010 11101101 11111111
//
// - +0x3579i16:   0b01111001 00110101
// - -0x3579i16:   0b10000111 11001010
//
// Or, the `!0x123579i32 + 1`, as documented. Since we're doing
// a big-endian representation, it means truncation is just taking the high
// words and going from there.

impl i256 {
    /// Create the 256-bit signed integer from a `u128`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u128(value: u128) -> Self {
        let (lo, hi) = math::as_uwide_i128(value);
        Self::new(lo, hi)
    }

    /// Create the 256-bit signed integer from an `u256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u256(value: u256) -> Self {
        value.as_i256()
    }

    /// Create the 256-bit signed integer from an `u256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_unsigned(value: u256) -> Self {
        Self::from_u256(value)
    }

    /// Create the 256-bit signed integer from an `i128`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_i128(value: i128) -> Self {
        let (lo, hi) = math::as_iwide_i128(value);
        Self::new(lo, hi)
    }

    /// Create the 256-bit signed integer from an `i256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_i256(value: i256) -> Self {
        value
    }

    /// Convert the 256-bit signed integer to an `u128`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u128(&self) -> u128 {
        math::as_unarrow_i128(self.low(), self.high())
    }

    /// Convert the 256-bit signed integer to an `u256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u256(&self) -> u256 {
        let (lo, hi) = math::wide_cast_i128(self.low(), self.high());
        u256::new(lo, hi)
    }

    /// Convert the 256-bit signed integer to an `u256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_unsigned(&self) -> u256 {
        self.as_u256()
    }

    /// Convert the 256-bit signed integer to an `i128`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i128(&self) -> i128 {
        math::as_inarrow_i128(self.low(), self.high())
    }

    /// Convert the 256-bit signed integer to an `i256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i256(&self) -> i256 {
        *self
    }

    /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn wrapping_add_uwide(self, n: UWide) -> Self {
        let (lo, hi) = math::wrapping_add_uwide_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn overflowing_add_uwide(self, n: UWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_add_uwide_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Add the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn wrapping_add_iwide(self, n: IWide) -> Self {
        let (lo, hi) = math::wrapping_add_iwide_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Add the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn overflowing_add_iwide(self, n: IWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_add_iwide_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn wrapping_sub_uwide(self, n: UWide) -> Self {
        let (lo, hi) = math::wrapping_sub_uwide_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn overflowing_sub_uwide(self, n: UWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_sub_uwide_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Subtract the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn wrapping_sub_iwide(self, n: IWide) -> Self {
        let (lo, hi) = math::wrapping_sub_iwide_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Subtract the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn overflowing_sub_iwide(self, n: IWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_sub_iwide_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn wrapping_mul_uwide(self, n: UWide) -> Self {
        let (lo, hi) = math::wrapping_mul_uwide_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn overflowing_mul_uwide(self, n: UWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_mul_uwide_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Multiply the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn wrapping_mul_iwide(self, n: IWide) -> Self {
        let (lo, hi) = math::wrapping_mul_iwide_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Multiply the 256-bit integer by a wide, 128-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn overflowing_mul_iwide(self, n: IWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_mul_iwide_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Multiply the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn wrapping_mul_ulimb(self, n: ULimb) -> Self {
        let (lo, hi) = math::wrapping_mul_ulimb_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Multiply the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn overflowing_mul_ulimb(self, n: ULimb) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_mul_ulimb_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Multiply the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn wrapping_mul_ilimb(self, n: ILimb) -> Self {
        let (lo, hi) = math::wrapping_mul_ilimb_i128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Multiply the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn overflowing_mul_ilimb(self, n: ILimb) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_mul_ilimb_i128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`wrapping_div_rem`]
    /// or [`wrapping_div_rem_ulimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`wrapping_div_rem`]: Self::wrapping_div_rem
    /// [`wrapping_div_rem_ulimb`]: Self::wrapping_div_rem_ulimb
    #[inline]
    pub fn wrapping_div_rem_uwide(self, n: UWide) -> (Self, UWide) {
        let x = self.wrapping_abs().as_u256().to_le_limbs();
        let (div, rem) = math::div_rem_wide(&x, n);
        let div = u256::from_le_limbs(div).as_i256();
        // rem is always positive: `-65 % 64` is 63
        (div, rem)
    }

    /// Div/Rem the 256-bit integer by a wide, 64-bit signed factor.
    ///
    /// This is a convenience function: always prefer [`wrapping_div_rem`]
    /// or [`wrapping_div_rem_ilimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`wrapping_div_rem`]: Self::wrapping_div_rem
    /// [`wrapping_div_rem_ilimb`]: Self::wrapping_div_rem_ilimb
    #[inline]
    pub fn wrapping_div_rem_iwide(self, n: IWide) -> (Self, IWide) {
        let x = self.wrapping_abs().as_u256().to_le_limbs();
        let (div, rem) = math::div_rem_wide(&x, n.wrapping_abs() as UWide);
        let mut div = u256::from_le_limbs(div).as_i256();
        let mut rem = rem as IWide;

        // convert to our correct signs, get the product
        if self.is_negative() != n.is_negative() {
            div = div.wrapping_neg();
        }
        if self.is_negative() {
            rem = rem.wrapping_neg();
        }

        (div, rem)
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do. This always
    /// wraps, which can never happen in practice.
    #[inline]
    pub fn wrapping_div_rem_ulimb(self, n: ULimb) -> (Self, ULimb) {
        let x = self.wrapping_abs().as_u256().to_le_limbs();
        let (div, rem) = math::div_rem_limb(&x, n);
        let div = u256::from_le_limbs(div).as_i256();
        // rem is always positive: `-65 % 64` is 63
        (div, rem)
    }

    /// Div/Rem the 256-bit integer by a 64-bit signed factor.
    ///
    /// This allows optimizations a full division cannot do. This always
    /// wraps, which can never happen in practice.
    #[inline]
    pub fn wrapping_div_rem_ilimb(self, n: ILimb) -> (Self, ILimb) {
        let x = self.wrapping_abs().as_u256().to_le_limbs();
        let (div, rem) = math::div_rem_limb(&x, n.wrapping_abs() as ULimb);
        let mut div = u256::from_le_limbs(div).as_i256();
        let mut rem = rem as ILimb;

        // convert to our correct signs, get the product
        if self.is_negative() != n.is_negative() {
            div = div.wrapping_neg();
        }
        if self.is_negative() {
            rem = rem.wrapping_neg();
        }

        (div, rem)
    }
}

int_traits_define!(i256);

impl From<bool> for i256 {
    #[inline(always)]
    fn from(small: bool) -> Self {
        Self::new(small as u128, 0)
    }
}

impl From<char> for i256 {
    #[inline(always)]
    fn from(c: char) -> Self {
        Self::new(c as u128, 0)
    }
}

from_trait_define!(i256, u8, from_u8);
from_trait_define!(i256, u16, from_u16);
from_trait_define!(i256, u32, from_u32);
from_trait_define!(i256, u64, from_u64);
from_trait_define!(i256, u128, from_u128);
from_trait_define!(i256, i8, from_i8);
from_trait_define!(i256, i16, from_i16);
from_trait_define!(i256, i32, from_i32);
from_trait_define!(i256, i64, from_i64);
from_trait_define!(i256, i128, from_i128);

macro_rules! shift_const_impl {
    (@shl $value:ident, $shift:ident) => {{
        let (lo, hi) = math::shl_i128($value.low(), $value.high(), $shift as u32);
        Self::new(lo, hi)
    }};

    (@shr $value:ident, $shift:ident) => {{
        let (lo, hi) = math::shr_i128($value.low(), $value.high(), $shift as u32);
        Self::new(lo, hi)
    }};

    (@nomod $t:ty, $shl:ident, $shr:ident) => (
        /// Const evaluation of shl.
        #[inline(always)]
        pub const fn $shl(self, other: $t) -> Self {
            let other = other as u32;
            shift_const_impl!(@shl self, other)
        }

        /// Const evaluation of shr.
        pub const fn $shr(self, other: $t) -> Self {
            let other = other as u32;
            shift_const_impl!(@shr self, other)
        }
    );

    ($t:ty, $shl:ident, $shr:ident) => (
        /// Const evaluation of shl.
        ///
        /// This behavior is wrapping: if `other >= 256`, this wraps.
        #[inline(always)]
        pub const fn $shl(self, other: $t) -> Self {
            debug_assert!(other < 256, "attempt to shift left with overflow");
            let other = other as u32;
            shift_const_impl!(@shl self, other)
        }

        /// Const evaluation of shr.
        ///
        /// This behavior is wrapping: if `other >= 256`, this wraps.
        pub const fn $shr(self, other: $t) -> Self {
            debug_assert!(other < 256, "attempt to shift right with overflow");
            let other = other as u32;
            shift_const_impl!(@shr self, other)
        }
    );

    (@256 $t:ty, $shl:ident, $shr:ident) => (
        /// Const evaluation of shl.
        ///
        /// This behavior is wrapping: if `other >= 256`, this wraps.
        #[inline(always)]
        pub const fn $shl(self, other: $t) -> Self {
            let max = u256::from_u16(256);
            let other = other.as_u256();
            debug_assert!(other.lt_const(max), "attempt to shift left with overflow");
            let shift = (other.low() & (u32::MAX as u128)) as u32;
            shift_const_impl!(@shl self, shift)
        }

        /// Const evaluation of shr.
        ///
        /// This behavior is wrapping: if `other >= 256`, this wraps.
        pub const fn $shr(self, other: $t) -> Self {
            let max = u256::from_u16(256);
            let other = other.as_u256();
            debug_assert!(other.lt_const(max), "attempt to shift left with overflow");
            let shift = (other.low() & (u32::MAX as u128)) as u32;
            shift_const_impl!(@shr self, shift)
        }
    );
}

// Const implementations for Shl
impl i256 {
    shift_const_impl!(@nomod i8, shl_i8, shr_i8);
    shift_const_impl!(i16, shl_i16, shr_i16);
    shift_const_impl!(i32, shl_i32, shr_i32);
    shift_const_impl!(i64, shl_i64, shr_i64);
    shift_const_impl!(i128, shl_i128, shr_i128);
    shift_const_impl!(@256 i256, shl_i256, shr_i256);
    shift_const_impl!(isize, shl_isize, shr_isize);
    shift_const_impl!(@nomod u8, shl_u8, shr_u8);
    shift_const_impl!(u16, shl_u16, shr_u16);
    shift_const_impl!(u32, shl_u32, shr_u32);
    shift_const_impl!(u64, shl_u64, shr_u64);
    shift_const_impl!(u128, shl_u128, shr_u128);
    shift_const_impl!(@256 u256, shl_u256, shr_u256);
    shift_const_impl!(usize, shl_usize, shr_usize);
}

impl Shl for i256 {
    type Output = Self;

    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shl(self, other: Self) -> Self::Output {
        let shift = other.low() & (u32::MAX as u128);
        shift_const_impl!(@shl self, shift)
    }
}

ref_trait_define!(i256, Shl, shl, other: &i256);
binop_ref_trait_define!(i256, Shl, shl);

impl Shr for i256 {
    type Output = Self;

    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shr(self, other: Self) -> Self::Output {
        let shift = other.low() & (u32::MAX as u128);
        shift_const_impl!(@shr self, shift)
    }
}

ref_trait_define!(i256, Shr, shr, other: &i256);
binop_ref_trait_define!(i256, Shr, shr);

macro_rules! shift_impl {
    (@mod $($t:ty)*) => ($(
        impl Shl<$t> for i256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shl(self, other: $t) -> Self::Output {
                let shift = other % 256;
                shift_const_impl!(@shl self, shift)
            }
        }

        impl Shr<$t> for i256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shr(self, other: $t) -> Self::Output {
                let shift = other % 256;
                shift_const_impl!(@shr self, shift)
            }
        }
    )*);

    (@nomod $($t:ty)*) => ($(
        impl Shl<$t> for i256 {
            type Output = Self;

            #[inline(always)]
            fn shl(self, other: $t) -> Self::Output {
                shift_const_impl!(@shl self, other)
            }
        }

        impl Shr<$t> for i256 {
            type Output = Self;

            #[inline(always)]
            fn shr(self, other: $t) -> Self::Output {
                shift_const_impl!(@shr self, other)
            }
        }
    )*);

    (@256 $($t:ty)*) => ($(
        impl Shl<$t> for i256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shl(self, other: $t) -> Self::Output {
                let shift = other % u256::from_u16(256);
                let shift = shift.as_u32();
                shift_const_impl!(@shl self, shift)
            }
        }

        impl Shr<$t> for i256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shr(self, other: $t) -> Self::Output {
                let shift = other % u256::from_u16(256);
                let shift = shift.as_u32();
                shift_const_impl!(@shr self, shift)
            }
        }
    )*);

    ($($t:ty)*) => ($(
        impl Shl<&$t> for i256 {
            type Output = <Self as Shl>::Output;

            #[inline(always)]
            fn shl(self, other: &$t) -> Self::Output {
                self.shl(*other)
            }
        }

        impl ShlAssign<$t> for i256 {
            #[inline(always)]
            fn shl_assign(&mut self, other: $t) {
                *self = self.shl(other);
            }
        }

        impl ShlAssign<&$t> for i256 {
            #[inline(always)]
            fn shl_assign(&mut self, other: &$t) {
                *self = self.shl(other);
            }
        }

        impl Shr<&$t> for i256 {
            type Output = <Self as Shr>::Output;

            #[inline(always)]
            fn shr(self, other: &$t) -> Self::Output {
                self.shr(*other)
            }
        }

        impl ShrAssign<$t> for i256 {
            #[inline(always)]
            fn shr_assign(&mut self, other: $t) {
                *self = self.shr(other);
            }
        }

        impl ShrAssign<&$t> for i256 {
            #[inline(always)]
            fn shr_assign(&mut self, other: &$t) {
                *self = self.shr(other);
            }
        }
    )*);
}

shift_impl! { @nomod i8 u8 }
shift_impl! { @mod i16 i32 i64 i128 isize u16 u32 u64 u128 usize }
shift_impl! { @256 u256 }
shift_impl! { i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 u256 usize }

impl TryFrom<u256> for i256 {
    type Error = TryFromIntError;

    #[inline(always)]
    fn try_from(u: u256) -> Result<Self, TryFromIntError> {
        if u < Self::MAX.as_u256() {
            Ok(Self::from_u256(u))
        } else {
            Err(TryFromIntError {})
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ParseIntError;

    #[inline(always)]
    fn parse(expected: i256, radix: u32, s: &str) {
        // check a full roundtrip
        let res: Result<i256, ParseIntError> = i256::from_str_radix(s, radix);
        assert!(res.is_ok());
        let actual = res.unwrap();
        assert_eq!(expected, actual);

        let as_str = actual.to_string();
        let res: Result<i256, ParseIntError> = i256::from_str_radix(&as_str, 10);
        assert!(res.is_ok());
        let actual = res.unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn from_str_radix_test() {
        let cases = [
            (
                i256::MIN,
                10,
                "-57896044618658097711785492504343953926634992332820282019728792003956564819968",
            ),
            (
                i256::MAX,
                10,
                "+57896044618658097711785492504343953926634992332820282019728792003956564819967",
            ),
            (0xffffffffffffffffi128.into(), 16, "+ffffffffffffffff"),
            (0x123456789ab123i128.into(), 10, "5124095576027427"),
            (0x123456789ab123i128.into(), 16, "+123456789ab123"),
            ((-15i128).into(), 10, "-15"),
            ((-255i128).into(), 16, "-FF"),
            (255i128.into(), 16, "+FF"),
        ];
        for case in cases {
            parse(case.0, case.1, case.2);
        }

        let failing = [
            (16, "-0xFF"),
            (16, "+0xFF"),
            (16, "0xFF"),
            (10, "FF"),
            (10, "a9"),
            (10, "12.34"),
            (10, "1234_67"),
            (10, "57896044618658097711785492504343953926634992332820282019728792003956564819968"),
            (10, "115792089237316195423570985008687907853269984665640564039457584007913129639935"),
            (10, "115792089237316195423570985008687907853269984665640564039457584007913129639936"),
            (16, "+ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"),
        ];
        for case in failing {
            let res: Result<i256, ParseIntError> = i256::from_str_radix(case.1, case.0);
            assert!(res.is_err());
        }
    }

    #[test]
    #[should_panic]
    fn from_str_radix_neg_test() {
        _ = i256::from_str_radix("-1F", 10).unwrap();
    }
}
