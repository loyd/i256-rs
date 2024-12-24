//! An unsigned 256-bit integer type.
//!
//! This aims to have feature parity with Rust's unsigned
//! integer types, such as [u32][core::u32]. The documentation
//! is based off of [u32][core::u32] for each method/member.
//!
//! A large portion of the implementation for helper functions
//! are based off of the Rust core implementation, such as for
//! [`checked_pow`][u128::checked_pow], [`isqrt`][u128::isqrt],
//! and more. Any non-performance critical functions, or those
//! crucial to parsing or serialization ([`add`][`u256::add`],
//! [`mul`][`u256::mul`], [`div`][`u256::div`], and
//! [`sub`][`u256::sub`]), as well as their `wrapping_*`,
//! `checked_*`, `overflowing_*` and `*_wide` variants are
//! likely based on the core implementations.

use core::cmp::Ordering;
use core::str::{FromStr, Utf8Error};
use core::{fmt, str};
use core::{ops::*, panic};

use super::macros::from_str_radix_impl;
use crate::error::{ParseIntError, TryFromIntError};
use crate::i256;
use crate::ints::i256::lt as i256_lt;
use crate::math::{self, ILimb, IWide, ULimb, UWide, LIMBS};
use crate::numtypes::*;

// FIXME: Add support for [Saturating][core::num::Saturating] and
// [Wrapping][core::num::Wrapping] when we drop support for <1.74.0.

/// The 256-bit unsigned integer type.
///
/// The high and low words depend on the target endianness.
/// Conversion to and from big endian should be done via
/// [`to_le_bytes`] and [`to_be_bytes`]. or using
/// [`high`] and [`low`].
///
/// Our formatting specifications are limited: we ignore a
/// lot of settings, and only respect [`alternate`] among the
/// formatter flags. So, we implement all the main formatters
/// ([`Binary`], etc.), but ignore all flags like `width`.
///
/// Note that this type is **NOT** safe in FFIs, since it uses
/// [`128-bit`] integers under the hood which are implementation-
/// defined and not FFI-safe. If you would like to use convert
/// this to an FFI, use [`to_le_bytes`] and [`to_be_bytes`].
///
/// [`to_le_bytes`]: i256::to_le_bytes
/// [`to_be_bytes`]: i256::to_be_bytes
/// [`high`]: i256::high
/// [`low`]: i256::low
/// [`alternate`]: fmt::Formatter::alternate
/// [`Binary`]: fmt::Binary
/// [`128-bit`]: https://rust-lang.github.io/unsafe-code-guidelines/layout/scalars.html#fixed-width-integer-types
#[allow(non_camel_case_types)]
#[derive(Copy, Clone, Default, PartialEq, Eq, Hash)]
pub struct u256 {
    // NOTE: This is currently FFI-safe (if we did repr(C)) but we
    // intentionally make  no guarantees so we're free to re-arrange
    // the layout.
    limbs: [ULimb; LIMBS],
}

impl u256 {
    /// The smallest value that can be represented by this integer type.
    ///
    /// See [`u128::MIN`].
    pub const MIN: Self = Self::new(0, 0);

    /// The largest value that can be represented by this integer type
    /// (2<sup>256</sup> - 1).
    ///
    /// See [`u128::MAX`].
    pub const MAX: Self = Self::new(u128::MAX, u128::MAX);

    /// The size of this integer type in bits.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use i256::u256;
    /// assert_eq!(u256::BITS, 256);
    /// ```
    ///
    /// See [`u128::BITS`].
    pub const BITS: u32 = 256;

    /// Returns the number of ones in the binary representation of `self`.
    ///
    /// See [`u128::count_ones`].
    #[inline(always)]
    pub const fn count_ones(self) -> u32 {
        self.high().count_ones() + self.low().count_ones()
    }

    /// Returns the number of zeros in the binary representation of `self`.
    ///
    /// See [`u128::count_zeros`].
    #[inline(always)]
    pub const fn count_zeros(self) -> u32 {
        not(self).count_ones()
    }

    /// Returns the number of leading zeros in the binary representation of
    /// `self`.
    ///
    /// Depending on what you're doing with the value, you might also be
    /// interested in the `ilog2` function which returns a consistent
    /// number, even if the type widens.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use i256::u256;
    /// let n = u256::MAX >> 2i32;
    /// assert_eq!(n.leading_zeros(), 2);
    ///
    /// let zero = u256::MIN;
    /// assert_eq!(zero.leading_zeros(), 256);
    ///
    /// let max = u256::MAX;
    /// assert_eq!(max.leading_zeros(), 0);
    /// ```
    ///
    /// See [`u128::leading_zeros`].
    #[inline(always)]
    pub const fn leading_zeros(self) -> u32 {
        let mut leading = self.high().leading_zeros();
        if leading == u128::BITS {
            leading += self.low().leading_zeros();
        }
        leading
    }

    /// Returns the number of trailing zeros in the binary representation of
    /// `self`.
    ///
    /// See [`u128::trailing_zeros`].
    #[inline(always)]
    pub const fn trailing_zeros(self) -> u32 {
        let mut trailing = self.low().trailing_zeros();
        if trailing == u128::BITS {
            trailing += self.high().trailing_zeros();
        }
        trailing
    }

    /// Returns the number of leading ones in the binary representation of
    /// `self`.
    ///
    /// See [`u128::leading_ones`].
    #[inline(always)]
    pub const fn leading_ones(self) -> u32 {
        not(self).leading_zeros()
    }

    /// Returns the number of trailing ones in the binary representation of
    /// `self`.
    ///
    /// See [`u128::trailing_ones`].
    #[inline(always)]
    pub const fn trailing_ones(self) -> u32 {
        not(self).trailing_zeros()
    }

    /// Shifts the bits to the left by a specified amount, `n`,
    /// wrapping the truncated bits to the end of the resulting integer.
    ///
    /// Please note this isn't the same operation as the `<<` shifting operator!
    ///
    /// See [`u128::rotate_left`].
    #[inline(always)]
    pub const fn rotate_left(self, n: u32) -> Self {
        let (lo, hi) = math::rotate_left_u128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Shifts the bits to the right by a specified amount, `n`,
    /// wrapping the truncated bits to the beginning of the resulting
    /// integer.
    ///
    /// Please note this isn't the same operation as the `>>` shifting operator!
    ///
    /// See [`u128::rotate_right`].
    #[inline(always)]
    pub const fn rotate_right(self, n: u32) -> Self {
        let (lo, hi) = math::rotate_right_u128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Reverses the byte order of the integer.
    ///
    /// See [`u128::swap_bytes`].
    #[inline(always)]
    pub const fn swap_bytes(self) -> Self {
        let (lo, hi) = math::swap_bytes_u128(self.low(), self.high());
        Self::new(lo, hi)
    }

    /// Reverses the order of bits in the integer. The least significant
    /// bit becomes the most significant bit, second least-significant bit
    /// becomes second most-significant bit, etc.
    ///
    /// See [`u128::reverse_bits`].
    #[inline(always)]
    pub const fn reverse_bits(self) -> Self {
        let (lo, hi) = math::reverse_bits_u128(self.low(), self.high());
        Self::new(lo, hi)
    }

    /// Converts an integer from big endian to the target's endianness.
    ///
    /// On big endian this is a no-op. On little endian the bytes are
    /// swapped.
    ///
    /// See [`u128::from_be`].
    #[inline(always)]
    pub const fn from_be(x: Self) -> Self {
        if cfg!(target_endian = "big") {
            x
        } else {
            x.swap_bytes()
        }
    }

    /// Converts an integer from little endian to the target's endianness.
    ///
    /// On little endian this is a no-op. On big endian the bytes are
    /// swapped.
    ///
    /// See [`u128::from_le`].
    #[inline(always)]
    pub const fn from_le(x: Self) -> Self {
        if cfg!(target_endian = "little") {
            x
        } else {
            x.swap_bytes()
        }
    }

    /// Converts `self` to big endian from the target's endianness.
    ///
    /// On big endian this is a no-op. On little endian the bytes are
    /// swapped.
    ///
    /// See [`u128::to_be`].
    #[inline(always)]
    pub const fn to_be(self) -> Self {
        if cfg!(target_endian = "big") {
            self
        } else {
            self.swap_bytes()
        }
    }

    /// Converts `self` to little endian from the target's endianness.
    ///
    /// On little endian this is a no-op. On big endian the bytes are
    /// swapped.
    ///
    /// See [`u128::to_le`].
    #[inline(always)]
    pub const fn to_le(self) -> Self {
        if cfg!(target_endian = "little") {
            self
        } else {
            self.swap_bytes()
        }
    }

    /// Checked integer addition. Computes `self + rhs`, returning `None`
    /// if overflow occurred.
    ///
    /// See [`u128::checked_add`].
    #[inline(always)]
    pub const fn checked_add(self, rhs: Self) -> Option<Self> {
        let (value, overflowed) = self.overflowing_add(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked addition with a signed integer. Computes `self + rhs`,
    /// returning `None` if overflow occurred.
    ///
    /// See [`u128::checked_add_signed`].
    #[inline(always)]
    pub const fn checked_add_signed(self, rhs: i256) -> Option<Self> {
        let (value, overflowed) = self.overflowing_add_signed(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked integer subtraction. Computes `self - rhs`, returning `None`
    /// if overflow occurred.
    ///
    /// See [`u128::checked_sub`].
    #[inline(always)]
    pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
        let (value, overflowed) = self.overflowing_sub(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked integer multiplication. Computes `self * rhs`, returning `None`
    /// if overflow occurred.
    ///
    /// See [`u128::checked_mul`].
    #[inline(always)]
    pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
        let (value, overflowed) = self.overflowing_mul(rhs);
        if !overflowed {
            Some(value)
        } else {
            None
        }
    }

    /// Checked integer division. Computes `self / rhs`, returning `None`
    /// if `rhs == 0`.
    ///
    /// See [`u128::checked_div`].
    #[inline(always)]
    pub fn checked_div(self, rhs: Self) -> Option<Self> {
        if eq(rhs, Self::MIN) {
            None
        } else {
            Some(self.wrapping_div(rhs))
        }
    }

    /// Performs Euclidean division.
    ///
    /// Since, for the positive integers, all common
    /// definitions of division are equal, this
    /// is exactly equal to `self / rhs`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::div_euclid`].
    #[inline(always)]
    pub fn div_euclid(self, rhs: Self) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div_euclid(rhs)
        } else {
            self.checked_div_euclid(rhs).expect("attempt to divide with overflow")
        }
    }

    /// Checked Euclidean division. Computes `self.div_euclid(rhs)`,
    /// returning `None` if `rhs == 0`.
    ///
    /// See [`u128::checked_div_euclid`].
    #[inline(always)]
    pub fn checked_div_euclid(self, rhs: Self) -> Option<Self> {
        if eq(rhs, Self::MIN) {
            None
        } else {
            Some(self.wrapping_div_euclid(rhs))
        }
    }

    /// Checked integer division. Computes `self % rhs`, returning `None`
    /// if `rhs == 0`.
    ///
    /// See [`u128::checked_rem`].
    #[inline(always)]
    pub fn checked_rem(self, rhs: Self) -> Option<Self> {
        if eq(rhs, Self::MIN) {
            None
        } else {
            Some(self.wrapping_rem(rhs))
        }
    }

    /// Calculates the least remainder of `self (mod rhs)`.
    ///
    /// Since, for the positive integers, all common
    /// definitions of division are equal, this
    /// is exactly equal to `self % rhs`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::rem_euclid`].
    #[inline(always)]
    pub fn rem_euclid(self, rhs: Self) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_rem(rhs)
        } else {
            self.checked_rem_euclid(rhs).expect("attempt to divide by zero")
        }
    }

    /// Checked Euclidean modulo. Computes `self.rem_euclid(rhs)`,
    /// returning `None` if `rhs == 0`.
    ///
    /// See [`u128::checked_rem_euclid`].
    #[inline(always)]
    pub fn checked_rem_euclid(self, rhs: Self) -> Option<Self> {
        if eq(rhs, Self::MIN) {
            None
        } else {
            Some(self.wrapping_rem_euclid(rhs))
        }
    }

    /// Returns the logarithm of the number with respect to an arbitrary base,
    /// rounded down.
    ///
    /// This method might not be optimized owing to implementation details;
    /// `ilog2` can produce results more efficiently for base 2, and `ilog10`
    /// can produce results more efficiently for base 10.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is zero, or if `base` is less than 2.
    ///
    /// See [`u128::ilog`].
    #[inline(always)]
    pub fn ilog(self, base: Self) -> u32 {
        if let Some(log) = self.checked_ilog(base) {
            log
        } else {
            panic!("argument of integer logarithm must be positive")
        }
    }

    /// Returns the base 2 logarithm of the number, rounded down.
    ///
    /// # Panics
    ///
    /// This function will panic if `self` is zero.
    ///
    /// See [`u128::ilog2`].
    #[inline(always)]
    pub const fn ilog2(self) -> u32 {
        if let Some(log) = self.checked_ilog2() {
            log
        } else {
            panic!("argument of integer logarithm must be positive")
        }
    }

    // FIXME: Stabilize when our MSRV goes to `1.67.0+`.
    // /// Returns the base 10 logarithm of the number, rounded down.
    // ///
    // /// # Panics
    // ///
    // /// This function will panic if `self` is zero.
    // #[inline(always)]
    // pub fn ilog10(self) -> u32 {
    //     if let Some(log) = self.checked_ilog10() {
    //         log
    //     } else {
    //         panic!("argument of integer logarithm must be positive")
    //     }
    // }

    /// Returns the logarithm of the number with respect to an arbitrary base,
    /// rounded down.
    ///
    /// Returns `None` if the number is zero, or if the base is not at least 2.
    ///
    /// This method might not be optimized owing to implementation details;
    /// `checked_ilog2` can produce results more efficiently for base 2, and
    /// `checked_ilog10` can produce results more efficiently for base 10.
    ///
    /// See [`u128::checked_ilog`].
    #[inline(always)]
    pub fn checked_ilog(self, base: Self) -> Option<u32> {
        let zero = Self::from_u8(0);
        if self == zero || base <= zero || lt(self, base) {
            return None;
        }

        // Since base >= self, n >= 1
        let mut n = 1;
        let mut r = base;

        // Optimization for 128+ bit wide integers.
        if Self::BITS >= 128 {
            // The following is a correct lower bound for ⌊log(base,self)⌋ because
            //
            // log(base,self) = log(2,self) / log(2,base)
            //                ≥ ⌊log(2,self)⌋ / (⌊log(2,base)⌋ + 1)
            //
            // hence
            //
            // ⌊log(base,self)⌋ ≥ ⌊ ⌊log(2,self)⌋ / (⌊log(2,base)⌋ + 1) ⌋ .
            n = self.ilog2() / (base.ilog2() + 1);
            r = base.pow(n);
        }

        while r <= self / base {
            n += 1;
            r *= base;
        }
        Some(n)
    }

    /// Returns the base 2 logarithm of the number, rounded down.
    ///
    /// Returns `None` if the number is zero.
    ///
    /// See [`u128::checked_ilog2`].
    #[inline(always)]
    pub const fn checked_ilog2(self) -> Option<u32> {
        match eq(self, Self::from_u8(0)) {
            true => None,
            false => Some(Self::BITS - 1 - self.leading_zeros()),
        }
    }

    // FIXME: Stabilize when our MSRV goes to `1.67.0+`.
    // /// Returns the base 10 logarithm of the number, rounded down.
    // ///
    // /// Returns `None` if the number is zero.
    // #[inline(always)]
    // pub fn checked_ilog10(self) -> Option<u32> {
    //     match eq(self, Self::from_u8(0)) {
    //         true => None,
    //         false => {
    //             // NOTE: The `ilog10` implementations for small
    //             // numbers are quite efficient, so we use those
    //             // when available. We want to get this to
    //             // a 128-bit integer in as few multiplications
    //             // as we can.
    //             let mut log = 0;
    //             let mut value = self;
    //             const E16: u64 = 10_000_000_000_000_000;
    //             while value.high() > 0 {
    //                 value = value.div_wide(E16);
    //                 log += 16;
    //             }
    //             let value: u128 = value.as_u128();
    //             Some(value.ilog10() + log)
    //         },
    //     }
    // }

    /// Checked negation. Computes `-self`, returning `None` unless `self ==
    /// 0`.
    ///
    /// Note that negating any positive integer will overflow.
    ///
    /// See [`u128::checked_neg`].
    #[inline(always)]
    pub const fn checked_neg(self) -> Option<Self> {
        if eq(self, Self::MIN) {
            Some(self)
        } else {
            None
        }
    }

    /// Checked shift left. Computes `self << rhs`, returning `None`
    /// if `rhs` is larger than or equal to the number of bits in `self`.
    ///
    /// See [`u128::checked_shl`].
    #[inline(always)]
    pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
        if rhs < Self::BITS {
            Some(self.shl_u32(rhs))
        } else {
            None
        }
    }

    /// Checked shift right. Computes `self >> rhs`, returning `None`
    /// if `rhs` is larger than or equal to the number of bits in `self`.
    ///
    /// See [`u128::checked_shr`].
    #[inline(always)]
    pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
        if rhs < Self::BITS {
            Some(self.shr_u32(rhs))
        } else {
            None
        }
    }

    /// Checked exponentiation. Computes `self.pow(exp)`, returning `None`
    /// if overflow occurred.
    ///
    /// See [`u128::checked_pow`].
    #[inline(always)]
    pub const fn checked_pow(self, base: u32) -> Option<Self> {
        match self.overflowing_pow(base) {
            (value, false) => Some(value),
            _ => None,
        }
    }

    /// Saturating integer addition. Computes `self + rhs`, saturating at
    /// the numeric bounds instead of overflowing.
    ///
    /// See [`u128::saturating_add`].
    #[inline(always)]
    pub const fn saturating_add(self, rhs: Self) -> Self {
        match self.checked_add(rhs) {
            Some(v) => v,
            None => Self::MAX,
        }
    }

    /// Saturating addition with a signed integer. Computes `self + rhs`,
    /// saturating at the numeric bounds instead of overflowing.
    ///
    /// See [`u128::saturating_add_signed`].
    #[inline]
    pub const fn saturating_add_signed(self, rhs: i256) -> Self {
        let is_negative = rhs.high() < 0;
        let (r, overflowed) = self.overflowing_add(Self::from_i256(rhs));
        if overflowed == is_negative {
            r
        } else if overflowed {
            Self::MAX
        } else {
            Self::MIN
        }
    }

    /// Saturating integer subtraction. Computes `self - rhs`, saturating
    /// at the numeric bounds instead of overflowing.
    ///
    /// See [`u128::saturating_sub`].
    #[inline(always)]
    pub const fn saturating_sub(self, rhs: Self) -> Self {
        match self.checked_sub(rhs) {
            Some(v) => v,
            None => Self::MIN,
        }
    }

    /// Saturating integer multiplication. Computes `self * rhs`,
    /// saturating at the numeric bounds instead of overflowing.
    ///
    /// See [`u128::saturating_mul`].
    #[inline(always)]
    pub const fn saturating_mul(self, rhs: Self) -> Self {
        match self.checked_mul(rhs) {
            Some(v) => v,
            None => Self::MAX,
        }
    }

    /// Saturating integer division. Computes `self / rhs`, saturating at the
    /// numeric bounds instead of overflowing.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::saturating_div`].
    #[inline(always)]
    pub fn saturating_div(self, rhs: Self) -> Self {
        // on unsigned types, there is no overflow in integer division
        self.wrapping_div(rhs)
    }

    /// Saturating integer exponentiation. Computes `self.pow(exp)`,
    /// saturating at the numeric bounds instead of overflowing.
    ///
    /// See [`u128::saturating_pow`].
    #[inline]
    pub const fn saturating_pow(self, exp: u32) -> Self {
        match self.checked_pow(exp) {
            Some(x) => x,
            None => Self::MAX,
        }
    }

    /// Wrapping (modular) addition. Computes `self + rhs`,
    /// wrapping around at the boundary of the type.
    ///
    /// See [`u128::wrapping_add`].
    #[inline(always)]
    pub const fn wrapping_add(self, rhs: Self) -> Self {
        let (lo, hi) = math::wrapping_add_u128(self.low(), self.high(), rhs.low(), rhs.high());
        u256::new(lo, hi)
    }

    /// Wrapping (modular) addition with a signed integer. Computes
    /// `self + rhs`, wrapping around at the boundary of the type.
    ///
    /// See [`u128::wrapping_add_signed`].
    #[inline(always)]
    pub const fn wrapping_add_signed(self, rhs: i256) -> Self {
        self.wrapping_add(Self::from_i256(rhs))
    }

    /// Wrapping (modular) subtraction. Computes `self - rhs`,
    /// wrapping around at the boundary of the type.
    ///
    /// See [`u128::wrapping_sub`].
    #[inline(always)]
    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        let (lo, hi) = math::wrapping_sub_u128(self.low(), self.high(), rhs.low(), rhs.high());
        u256::new(lo, hi)
    }

    /// Wrapping (modular) multiplication. Computes `self *
    /// rhs`, wrapping around at the boundary of the type.
    ///
    /// Many different algorithms were attempted, with a soft [`mulx`] approach
    /// (1), a flat, fixed-width long multiplication (2), and a
    /// short-circuiting long multiplication (3). Algorithm (3) had the best
    /// performance for 128-bit multiplication, however, algorithm (1) was
    /// better for smaller type sizes.
    ///
    /// This also optimized much better when multiplying by a single or a
    /// half-sized item: rather than using 4 limbs, if we're multiplying
    /// `(u128, u128) * u128`, we can use 2 limbs for the right operand, and
    /// for `(u128, u128) * u64`, only
    ///
    /// # Assembly
    ///
    /// For a 128-bit multiplication (2x `u64` + 2x `u64`), algorithm (1) had
    /// 6 `mul`, 6 `add`, and 6 bitshift instructions. Algorithm (3) had 10
    /// `mul`, 12 `add`, and 12 bitshift instructions in the worst case, with
    /// a minimum of 4 `mul` and 2 `add` instructions, along with a lot of
    /// branching. That is, it was almost never worth it.
    ///
    /// However, for 256-bit multiplication, the switch flips, with algorithm
    /// (1) having 10 `mul` and 14 `add` instructions. However, algorithm (3)
    /// has in the worst case 10 `mul` and 15 `add` instructions, however,
    /// because of branching in nearly every case, it has better performance
    /// and optimizes nicely for small multiplications.
    ///
    /// See [`u128::wrapping_mul`].
    ///
    /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
    #[inline(always)]
    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        // 128-Bit
        // -------
        // long_u64:
        //     push    r15
        //     push    r14
        //     push    rbx
        //     mov     r11, rdi
        //     shr     r11, 32
        //     mov     r8, rdx
        //     shr     r8, 32
        //     test    edi, edi
        //     je      .LBB0_1
        //     mov     ebx, edi
        //     mov     r9, rcx
        //     shr     r9, 32
        //     mov     eax, edx
        //     imul    rax, rbx
        //     mov     r10d, eax
        //     mov     r14, rax
        //     shr     r14, 32
        //     mov     rax, r8
        //     imul    rax, rbx
        //     add     rax, r14
        //     mov     r14, rax
        //     shr     r14, 32
        //     mov     r15d, ecx
        //     imul    r15, rbx
        //     imul    r9d, edi
        //     shl     r9, 32
        //     add     r9, r15
        //     add     r9, r14
        //     movabs  rdi, -4294967296
        //     test    r11, r11
        //     je      .LBB0_5
        // .LBB0_4:
        //     mov     ebx, edx
        //     imul    rbx, r11
        //     mov     eax, eax
        //     add     rax, rbx
        //     mov     rbx, rax
        //     shr     rbx, 32
        //     mov     r14, r8
        //     imul    r14, r11
        //     mov     r15d, r9d
        //     add     r15, r14
        //     add     r15, rbx
        //     mov     ebx, r15d
        //     imul    r11d, ecx
        //     shl     r11, 32
        //     add     r11, r15
        //     and     r11, rdi
        //     add     r11, r9
        //     and     r11, rdi
        //     or      r11, rbx
        //     mov     r9, r11
        // .LBB0_5:
        //     test    esi, esi
        //     je      .LBB0_7
        //     mov     ecx, esi
        //     mov     r11d, edx
        //     imul    r11, rcx
        //     mov     ecx, r9d
        //     add     rcx, r11
        //     mov     r11d, ecx
        //     imul    r8d, esi
        //     shl     r8, 32
        //     add     r8, rcx
        //     and     r8, rdi
        //     add     r8, r9
        //     and     r8, rdi
        //     or      r8, r11
        //     mov     r9, r8
        // .LBB0_7:
        //     shr     rsi, 32
        //     imul    edx, esi
        //     shl     rdx, 32
        //     test    rsi, rsi
        //     cmove   rdx, rsi
        //     add     rdx, r9
        //     shl     rax, 32
        //     or      rax, r10
        //     pop     rbx
        //     pop     r14
        //     pop     r15
        //     ret
        // .LBB0_1:
        //     xor     r9d, r9d
        //     xor     eax, eax
        //     xor     r10d, r10d
        //     movabs  rdi, -4294967296
        //     test    r11, r11
        //     jne     .LBB0_4
        //     jmp     .LBB0_5
        //
        // mulx_u64:
        //     mov     eax, edi
        //     imul    rcx, rdi
        //     shr     rdi, 32
        //     mov     r8d, edx
        //     mov     r9, rdx
        //     shr     r9, 32
        //     mov     r10, r8
        //     imul    r10, rax
        //     imul    rax, r9
        //     imul    r8, rdi
        //     imul    r9, rdi
        //     mov     edi, r10d
        //     shr     r10, 32
        //     add     r10, r8
        //     mov     r8d, r10d
        //     shr     r10, 32
        //     add     r8, rax
        //     mov     rax, r8
        //     shl     rax, 32
        //     or      rax, rdi
        //     shr     r8, 32
        //     imul    rdx, rsi
        //     add     rdx, rcx
        //     add     rdx, r9
        //     add     rdx, r10
        //     add     rdx, r8
        //     ret
        //
        // 256-Bit
        // -------
        // long_u128:
        //     push    r15
        //     push    r14
        //     push    r13
        //     push    r12
        //     push    rbx
        //     mov     r12, rdx
        //     mov     r15, qword ptr [rsp + 64]
        //     mov     r11, qword ptr [rsp + 56]
        //     mov     rbx, qword ptr [rsp + 48]
        //     test    rsi, rsi
        //     je      .LBB1_1
        //     mov     rax, rbx
        //     mul     rsi
        //     mov     r14, rdx
        //     mov     r9, rax
        //     mov     rax, r11
        //     mul     rsi
        //     mov     r13, rdx
        //     mov     r10, rax
        //     add     r10, r14
        //     adc     r13, 0
        //     mov     rax, r15
        //     mul     rsi
        //     mov     r14, rax
        //     imul    rsi, qword ptr [rsp + 72]
        //     add     r14, r13
        //     adc     rsi, rdx
        //     test    r12, r12
        //     je      .LBB1_5
        // .LBB1_4:
        //     mov     rax, rbx
        //     mul     r12
        //     mov     r13, rdx
        //     add     r10, rax
        //     adc     r13, 0
        //     mov     rax, r11
        //     mul     r12
        //     add     rax, r13
        //     adc     rdx, 0
        //     imul    r15, r12
        //     add     r14, rax
        //     adc     r15, rdx
        //     add     rsi, r15
        // .LBB1_5:
        //     test    rcx, rcx
        //     je      .LBB1_7
        //     mov     rax, rbx
        //     mul     rcx
        //     imul    r11, rcx
        //     add     r14, rax
        //     adc     r11, rdx
        //     add     rsi, r11
        // .LBB1_7:
        //     test    r8, r8
        //     je      .LBB1_9
        //     imul    r8, rbx
        //     add     rsi, r8
        // .LBB1_9:
        //     mov     qword ptr [rdi + 8], r10
        //     mov     qword ptr [rdi], r9
        //     mov     qword ptr [rdi + 24], rsi
        //     mov     qword ptr [rdi + 16], r14
        //     mov     rax, rdi
        //     pop     rbx
        //     pop     r12
        //     pop     r13
        //     pop     r14
        //     pop     r15
        //     ret
        // .LBB1_1:
        //     xor     esi, esi
        //     xor     r14d, r14d
        //     xor     r10d, r10d
        //     xor     r9d, r9d
        //     test    r12, r12
        //     jne     .LBB1_4
        //     jmp     .LBB1_5
        //
        // mulx_u128:
        //     push    rbp
        //     push    r15
        //     push    r14
        //     push    r13
        //     push    r12
        //     push    rbx
        //     mov     r13, rdx
        //     mov     r12, qword ptr [rsp + 56]
        //     mov     r14, qword ptr [rsp + 64]
        //     mov     rax, r12
        //     mul     rsi
        //     mov     qword ptr [rsp - 24], rdx
        //     mov     qword ptr [rsp - 8], rax
        //     mov     rax, r14
        //     mul     rsi
        //     mov     rbx, rax
        //     mov     qword ptr [rsp - 16], rdx
        //     mov     rax, r12
        //     mul     r13
        //     mov     r15, rdx
        //     mov     rbp, rax
        //     mov     rax, r14
        //     mul     r13
        //     mov     r10, rax
        //     mov     r9, rdx
        //     mov     rax, qword ptr [rsp + 72]
        //     imul    r13, rax
        //     mul     rsi
        //     mov     r11, rax
        //     add     rdx, r13
        //     imul    rsi, qword ptr [rsp + 80]
        //     add     rsi, rdx
        //     imul    r8, r12
        //     mov     rax, r12
        //     mul     rcx
        //     add     rdx, r8
        //     imul    r14, rcx
        //     add     r14, rdx
        //     add     rax, r10
        //     adc     r14, r9
        //     add     rax, r11
        //     adc     r14, rsi
        //     add     rbp, qword ptr [rsp - 24]
        //     adc     rax, r15
        //     adc     r14, 0
        //     add     rbp, rbx
        //     adc     rax, qword ptr [rsp - 16]
        //     mov     rcx, qword ptr [rsp - 8]
        //     mov     qword ptr [rdi], rcx
        //     mov     qword ptr [rdi + 8], rbp
        //     mov     qword ptr [rdi + 16], rax
        //     adc     r14, 0
        //     mov     qword ptr [rdi + 24], r14
        //     mov     rax, rdi
        //     pop     rbx
        //     pop     r12
        //     pop     r13
        //     pop     r14
        //     pop     r15
        //     pop     rbp
        //     ret
        let r = math::wrapping_mul_arr_u128(&self.to_le_limbs(), &rhs.to_le_limbs());
        Self::from_le_limbs(r)
    }

    /// Wrapping (modular) division. Computes `self / rhs`.
    ///
    /// Wrapped division on unsigned types is just normal division. There's
    /// no way wrapping could ever happen. This function exists so that all
    /// operations are accounted for in the wrapping operations.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::wrapping_div`].
    #[inline(always)]
    pub fn wrapping_div(self, rhs: Self) -> Self {
        self.wrapping_div_rem(rhs).0
    }

    /// Wrapping Euclidean division. Computes `self.div_euclid(rhs)`.
    ///
    /// Wrapped division on unsigned types is just normal division. There's
    /// no way wrapping could ever happen. This function exists so that all
    /// operations are accounted for in the wrapping operations. Since, for
    /// the positive integers, all common definitions of division are equal,
    /// this is exactly equal to `self.wrapping_div(rhs)`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::wrapping_div_euclid`].
    #[inline(always)]
    pub fn wrapping_div_euclid(self, rhs: Self) -> Self {
        self.wrapping_div(rhs)
    }

    /// Wrapping (modular) remainder. Computes `self % rhs`.
    ///
    /// Wrapped remainder calculation on unsigned types is just the regular
    /// remainder calculation. There's no way wrapping could ever happen.
    /// This function exists so that all operations are accounted for in the
    /// wrapping operations.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::wrapping_rem`].
    #[inline(always)]
    pub fn wrapping_rem(self, rhs: Self) -> Self {
        self.wrapping_div_rem(rhs).1
    }

    /// Wrapping Euclidean modulo. Computes `self.rem_euclid(rhs)`.
    ///
    /// Wrapped modulo calculation on unsigned types is just the regular
    /// remainder calculation. There's no way wrapping could ever happen.
    /// This function exists so that all operations are accounted for in the
    /// wrapping operations. Since, for the positive integers, all common
    /// definitions of division are equal, this is exactly equal to
    /// `self.wrapping_rem(rhs)`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::wrapping_rem_euclid`].
    #[inline(always)]
    pub fn wrapping_rem_euclid(self, rhs: Self) -> Self {
        self.wrapping_rem(rhs)
    }

    /// Wrapping (modular) negation. Computes `-self`,
    /// wrapping around at the boundary of the type.
    ///
    /// Since unsigned types do not have negative equivalents
    /// all applications of this function will wrap (except for `-0`).
    /// For values smaller than the corresponding signed type's maximum
    /// the result is the same as casting the corresponding signed value.
    /// Any larger values are equivalent to `MAX + 1 - (val - MAX - 1)` where
    /// `MAX` is the corresponding signed type's maximum.
    ///
    /// See [`u128::wrapping_neg`].
    #[inline(always)]
    pub const fn wrapping_neg(self) -> Self {
        Self::MIN.wrapping_sub(self)
    }

    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`,
    /// where `mask` removes any high-order bits of `rhs` that
    /// would cause the shift to exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-left; the
    /// RHS of a wrapping shift-left is restricted to the range
    /// of the type, rather than the bits shifted out of the LHS
    /// being returned to the other end. The primitive integer
    /// types all implement a [`rotate_left`](Self::rotate_left) function,
    /// which may be what you want instead.
    ///
    /// See [`u128::wrapping_shl`].
    #[inline(always)]
    pub const fn wrapping_shl(self, rhs: u32) -> Self {
        let (lo, hi) = math::shl_u128(self.low(), self.high(), rhs % 256);
        Self::new(lo, hi)
    }

    /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`,
    /// where `mask` removes any high-order bits of `rhs` that
    /// would cause the shift to exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-right; the
    /// RHS of a wrapping shift-right is restricted to the range
    /// of the type, rather than the bits shifted out of the LHS
    /// being returned to the other end. The primitive integer
    /// types all implement a [`rotate_right`](Self::rotate_right) function,
    /// which may be what you want instead.
    ///
    /// See [`u128::wrapping_shr`].
    #[inline(always)]
    pub const fn wrapping_shr(self, rhs: u32) -> Self {
        let (lo, hi) = math::shr_u128(self.low(), self.high(), rhs % 256);
        Self::new(lo, hi)
    }

    /// Wrapping (modular) exponentiation. Computes `self.pow(exp)`,
    /// wrapping around at the boundary of the type.
    ///
    /// See [`u128::wrapping_pow`].
    #[inline]
    pub const fn wrapping_pow(self, mut exp: u32) -> Self {
        if exp == 0 {
            return Self::from_u8(1);
        }
        let mut base = self;
        let mut acc = Self::from_u8(1);

        // NOTE: The exponent can never go to 0.
        loop {
            if (exp & 1) == 1 {
                acc = acc.wrapping_mul(base);
                // since exp!=0, finally the exp must be 1.
                if exp == 1 {
                    return acc;
                }
            }
            exp /= 2;
            base = base.wrapping_mul(base);
            debug_assert!(exp != 0, "logic error in exponentiation, will infinitely loop");
        }
    }

    /// Calculates `self` + `rhs`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    ///
    /// See [`u128::overflowing_add`].
    #[inline(always)]
    pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) =
            math::overflowing_add_u128(self.low(), self.high(), rhs.low(), rhs.high());
        (Self::new(lo, hi), overflowed)
    }

    /// Calculates `self` + `rhs` with a signed `rhs`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    ///
    /// See [`u128::overflowing_add_signed`].
    #[inline(always)]
    pub const fn overflowing_add_signed(self, rhs: i256) -> (Self, bool) {
        let is_negative = rhs.high() < 0;
        let (r, overflowed) = self.overflowing_add(Self::from_i256(rhs));
        (r, overflowed ^ is_negative)
    }

    /// Calculates `self` - `rhs`.
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    ///
    /// See [`u128::overflowing_sub`].
    #[inline(always)]
    pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) =
            math::overflowing_sub_u128(self.low(), self.high(), rhs.low(), rhs.high());
        (Self::new(lo, hi), overflowed)
    }

    /// Computes the absolute difference between `self` and `other`.
    ///
    /// See [`u128::abs_diff`].
    #[inline(always)]
    pub const fn abs_diff(self, other: Self) -> Self {
        if lt(self, other) {
            other.wrapping_sub(self)
        } else {
            self.wrapping_sub(other)
        }
    }

    /// Calculates the multiplication of `self` and `rhs`.
    ///
    /// Returns a tuple of the multiplication along with a boolean
    /// indicating whether an arithmetic overflow would occur. If an
    /// overflow would have occurred then the wrapped value is returned.
    ///
    /// Many different algorithms were attempted, with a soft [`mulx`] approach
    /// (1), a flat, fixed-width long multiplication (2), and a
    /// short-circuiting long multiplication (3). Algorithm (3) had the best
    /// performance for 128-bit multiplication, however, algorithm (1) was
    /// better for smaller type sizes.
    ///
    /// This also optimized much better when multiplying by a single or a
    /// half-sized item: rather than using 4 limbs, if we're multiplying
    /// `(u128, u128) * u128`, we can use 2 limbs for the right operand, and
    /// for `(u128, u128) * u64`, only 1 limb.
    ///
    /// * `x0` - The lower half of x.
    /// * `x1` - The upper half of x.
    /// * `y0` - The lower half of y.
    /// * `y1` - The upper half of y.
    ///
    /// # Assembly
    ///
    /// The analysis here is practically identical to that of [`wrapping_mul`].
    ///
    /// See [`u128::overflowing_mul`].
    ///
    /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
    /// [`wrapping_mul`]: Self::wrapping_mul
    #[inline(always)]
    pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let (r, overflow) = math::overflowing_mul_arr_u128(&self.to_le_limbs(), &rhs.to_le_limbs());
        (Self::from_le_limbs(r), overflow)
    }

    /// Calculates the divisor when `self` is divided by `rhs`.
    ///
    /// Returns a tuple of the divisor along with a boolean indicating
    /// whether an arithmetic overflow would occur. Note that for unsigned
    /// integers overflow never occurs, so the second value is always
    /// `false`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::overflowing_div`].
    #[inline(always)]
    pub fn overflowing_div(self, rhs: Self) -> (Self, bool) {
        if rhs == Self::from_u8(0) {
            (Self::MAX, true)
        } else {
            (self.wrapping_div(rhs), false)
        }
    }

    /// Calculates the quotient of Euclidean division `self.div_euclid(rhs)`.
    ///
    /// Returns a tuple of the divisor along with a boolean indicating
    /// whether an arithmetic overflow would occur. Note that for unsigned
    /// integers overflow never occurs, so the second value is always
    /// `false`.
    /// Since, for the positive integers, all common
    /// definitions of division are equal, this
    /// is exactly equal to `self.overflowing_div(rhs)`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::overflowing_div_euclid`].
    #[inline(always)]
    pub fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) {
        self.overflowing_div(rhs)
    }

    /// Calculates the remainder when `self` is divided by `rhs`.
    ///
    /// Returns a tuple of the remainder after dividing along with a boolean
    /// indicating whether an arithmetic overflow would occur. Note that for
    /// unsigned integers overflow never occurs, so the second value is
    /// always `false`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::overflowing_rem`].
    #[inline(always)]
    pub fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
        if rhs == Self::from_u8(0) {
            (Self::from_u8(0), true)
        } else {
            (self.wrapping_rem(rhs), false)
        }
    }

    /// Calculates the remainder `self.rem_euclid(rhs)` as if by Euclidean
    /// division.
    ///
    /// Returns a tuple of the modulo after dividing along with a boolean
    /// indicating whether an arithmetic overflow would occur. Note that for
    /// unsigned integers overflow never occurs, so the second value is
    /// always `false`.
    /// Since, for the positive integers, all common
    /// definitions of division are equal, this operation
    /// is exactly equal to `self.overflowing_rem(rhs)`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::overflowing_rem_euclid`].
    #[inline(always)]
    pub fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) {
        self.overflowing_rem(rhs)
    }

    /// Raises self to the power of `exp`, using exponentiation by squaring.
    ///
    /// Returns a tuple of the exponentiation along with a bool indicating
    /// whether an overflow happened.
    ///
    /// See [`u128::overflowing_pow`].
    #[inline]
    pub const fn overflowing_pow(self, mut exp: u32) -> (Self, bool) {
        if exp == 0 {
            return (Self::from_u8(1), false);
        }
        let mut base = self;
        let mut acc = Self::from_u8(1);
        let mut overflown = false;
        let mut r: (Self, bool);

        // NOTE: The exponent can never go to 0.
        loop {
            if (exp & 1) == 1 {
                r = acc.overflowing_mul(base);
                // since exp!=0, finally the exp must be 1.
                if exp == 1 {
                    r.1 |= overflown;
                    return r;
                }
                acc = r.0;
                overflown |= r.1;
            }
            exp /= 2;
            r = base.overflowing_mul(base);
            base = r.0;
            overflown |= r.1;
            debug_assert!(exp != 0, "logic error in exponentiation, will infinitely loop");
        }
    }

    /// Raises self to the power of `exp`, using exponentiation by squaring.
    ///
    /// See [`u128::pow`].
    #[inline]
    pub const fn pow(self, exp: u32) -> Self {
        // FIXME: If #111466 is stabilized, we can use that
        // and determine if overflow checks are enabled.
        self.wrapping_pow(exp)
    }

    // FIXME: Stabilize when our MSRV goes to `1.84.0+`.
    // /// Returns the square root of the number, rounded down.
    // #[inline]
    // pub const fn isqrt(self) -> Self {
    //     todo!();
    // }

    /// Calculates the quotient of `self` and `rhs`, rounding the result towards
    /// negative infinity.
    ///
    /// This is the same as performing `self / rhs` for all unsigned integers.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::div_floor`].
    #[inline(always)]
    pub fn div_floor(self, rhs: Self) -> Self {
        self.wrapping_div(rhs)
    }

    /// Calculates the quotient of `self` and `rhs`, rounding the result towards
    /// positive infinity.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::div_ceil`].
    #[inline]
    pub fn div_ceil(self, rhs: Self) -> Self {
        let (d, r) = self.wrapping_div_rem(rhs);
        if r.low() > 0 || r.high() > 0 {
            // NOTE: This can't overflow
            d.wrapping_add(Self::from_u8(1))
        } else {
            d
        }
    }

    /// Calculates the smallest value greater than or equal to `self` that
    /// is a multiple of `rhs`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// ## Overflow behavior
    ///
    /// On overflow, this function will panic if overflow checks are enabled
    /// (default in debug mode) and wrap if overflow checks are disabled
    /// (default in release mode).
    ///
    /// See [`u128::next_multiple_of`].
    #[inline]
    pub fn next_multiple_of(self, rhs: Self) -> Self {
        match self.wrapping_rem(rhs) {
            Self::MIN => self,
            r => self.wrapping_add(rhs.wrapping_sub(r)),
        }
    }

    /// Calculates the smallest value greater than or equal to `self` that
    /// is a multiple of `rhs`. Returns `None` if `rhs` is zero or the
    /// operation would result in overflow.
    ///
    /// See [`u128::checked_next_multiple_of`].
    #[inline]
    pub fn checked_next_multiple_of(self, rhs: Self) -> Option<Self> {
        match self.checked_rem(rhs) {
            None => None,
            Some(Self::MIN) => Some(self),
            // rhs - r cannot overflow because r is smaller than rhs
            Some(r) => self.checked_add(rhs.wrapping_sub(r)),
        }
    }

    /// Returns `true` if `self` is an integer multiple of `rhs`, and false
    /// otherwise.
    ///
    /// This function is equivalent to `self % rhs == 0`, except that it will
    /// not panic for `rhs == 0`. Instead, `0.is_multiple_of(0) == true`,
    /// and for any non-zero `n`, `n.is_multiple_of(0) == false`.
    #[inline]
    pub fn is_multiple_of(self, rhs: Self) -> bool {
        match rhs {
            Self::MIN => eq(self, Self::MIN),
            _ => eq(self.wrapping_rem(rhs), Self::MIN),
        }
    }

    /// Returns `true` if and only if `self == 2^k` for some `k`.
    ///
    /// See [`u128::is_power_of_two`].
    #[inline(always)]
    pub const fn is_power_of_two(self) -> bool {
        self.count_ones() == 1
    }

    #[inline]
    const fn one_less_than_next_power_of_two(self) -> Self {
        if le(self, Self::from_u8(1)) {
            return Self::MIN;
        }
        let p = self.wrapping_sub(Self::from_u8(1));
        let z = p.leading_zeros();
        Self::MAX.wrapping_shr(z)
    }

    /// Returns the smallest power of two greater than or equal to `self`.
    ///
    /// When return value overflows (i.e., `self > (1 << (N-1))` for type
    /// `uN`), it panics in debug mode and the return value is wrapped to 0 in
    /// release mode (the only situation in which this method can return 0).
    ///
    /// See [`u128::next_power_of_two`].
    #[inline]
    pub const fn next_power_of_two(self) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_next_power_of_two()
        } else {
            match self.checked_next_power_of_two() {
                Some(v) => v,
                None => panic!("attempt to add with overflow"),
            }
        }
    }

    /// Returns the smallest power of two greater than or equal to `self`. If
    /// the next power of two is greater than the type's maximum value,
    /// `None` is returned, otherwise the power of two is wrapped in `Some`.
    ///
    /// See [`u128::checked_next_power_of_two`].
    #[inline]
    pub const fn checked_next_power_of_two(self) -> Option<Self> {
        self.one_less_than_next_power_of_two().checked_add(Self::from_u8(1))
    }

    /// Returns the smallest power of two greater than or equal to `n`. If
    /// the next power of two is greater than the type's maximum value,
    /// the return value is wrapped to `0`.
    ///
    /// See [`u128::wrapping_next_power_of_two`].
    #[inline]
    pub const fn wrapping_next_power_of_two(self) -> Self {
        self.one_less_than_next_power_of_two().wrapping_add(Self::from_u8(1))
    }

    /// Returns the memory representation of this integer as a byte array in
    /// big-endian (network) byte order.
    ///
    /// See [`u128::to_be_bytes`].
    #[inline(always)]
    pub const fn to_be_bytes(self) -> [u8; 32] {
        math::from_limbs(self.to_be_limbs())
    }

    /// Returns the memory representation of this integer as a byte array in
    /// little-endian byte order.
    ///
    /// See [`u128::to_le_bytes`].
    #[inline(always)]
    pub const fn to_le_bytes(self) -> [u8; 32] {
        math::from_limbs(self.to_le_limbs())
    }

    /// Returns the memory representation of this integer as a byte array in
    /// native byte order.
    ///
    /// As the target platform's native endianness is used, portable code
    /// should use [`to_be_bytes`] or [`to_le_bytes`], as appropriate,
    /// instead.
    ///
    /// See [`u128::to_ne_bytes`].
    ///
    /// [`to_be_bytes`]: Self::to_be_bytes
    /// [`to_le_bytes`]: Self::to_le_bytes
    #[inline(always)]
    pub const fn to_ne_bytes(self) -> [u8; 32] {
        math::from_limbs(self.to_ne_limbs())
    }

    /// Returns the memory representation of this as a series of limbs in
    /// big-endian (network) byte order.
    #[inline(always)]
    pub const fn to_be_limbs(self) -> [ULimb; LIMBS] {
        self.to_be().limbs
    }

    /// Returns the memory representation of this as a series of limbs in
    /// little-endian byte order.
    #[inline(always)]
    pub const fn to_le_limbs(self) -> [ULimb; LIMBS] {
        self.to_le().limbs
    }

    /// Returns the memory representation of this as a series of limbs.
    ///
    /// As the target platform's native endianness is used, portable code
    /// should use [`to_be_limbs`] or [`to_le_limbs`], as appropriate,
    /// instead.
    ///
    /// [`to_be_limbs`]: Self::to_be_limbs
    /// [`to_le_limbs`]: Self::to_le_limbs
    #[inline(always)]
    pub const fn to_ne_limbs(self) -> [ULimb; LIMBS] {
        self.limbs
    }

    /// Creates a native endian integer value from its representation
    /// as a byte array in big endian.
    ///
    /// See [`u128::from_be_bytes`].
    #[inline(always)]
    pub const fn from_be_bytes(bytes: [u8; 32]) -> Self {
        Self::from_be_limbs(math::to_limbs(bytes))
    }

    /// Creates a native endian integer value from its representation
    /// as a byte array in little endian.
    ///
    /// See [`u128::from_le_bytes`].
    #[inline(always)]
    pub const fn from_le_bytes(bytes: [u8; 32]) -> Self {
        Self::from_le_limbs(math::to_limbs(bytes))
    }

    /// Creates a native endian integer value from its memory representation
    /// as a byte array in native endianness.
    ///
    /// As the target platform's native endianness is used, portable code
    /// likely wants to use [`from_be_bytes`] or [`from_le_bytes`], as
    /// appropriate instead.
    ///
    /// See [`u128::from_ne_bytes`].
    ///
    /// [`from_be_bytes`]: Self::from_be_bytes
    /// [`from_le_bytes`]: Self::from_le_bytes
    #[inline(always)]
    pub const fn from_ne_bytes(bytes: [u8; 32]) -> Self {
        Self::from_ne_limbs(math::to_limbs(bytes))
    }

    /// Creates a native endian integer value from its representation
    /// as limbs in big endian.
    #[inline(always)]
    pub const fn from_be_limbs(limbs: [ULimb; LIMBS]) -> Self {
        if cfg!(target_endian = "big") {
            Self::from_ne_limbs(limbs)
        } else {
            Self::from_ne_limbs(math::swap_limbs(limbs))
        }
    }

    /// Creates a native endian integer value from its representation
    /// as limbs in little endian.
    #[inline(always)]
    pub const fn from_le_limbs(limbs: [ULimb; LIMBS]) -> Self {
        if cfg!(target_endian = "big") {
            Self::from_ne_limbs(math::swap_limbs(limbs))
        } else {
            Self::from_ne_limbs(limbs)
        }
    }

    /// Creates a native endian integer value from its memory representation
    /// as limbs in native endianness.
    ///
    /// As the target platform's native endianness is used, portable code
    /// likely wants to use [`from_be_limbs`] or [`from_le_limbs`], as
    /// appropriate instead.
    ///
    /// [`from_be_limbs`]: Self::from_be_limbs
    /// [`from_le_limbs`]: Self::from_le_limbs
    #[inline(always)]
    pub const fn from_ne_limbs(limbs: [ULimb; LIMBS]) -> Self {
        Self {
            limbs,
        }
    }

    /// Converts a string slice in a given base to an integer.
    ///
    /// The string is expected to be an optional `+`
    /// sign followed by only digits. Leading and trailing non-digit characters
    /// (including whitespace) represent an error. Underscores (which are
    /// accepted in rust literals) also represent an error.
    ///
    /// Digits are a subset of these characters, depending on `radix`:
    /// * `0-9`
    /// * `a-z`
    /// * `A-Z`
    ///
    /// This only has rudimentary optimizations.
    ///
    /// # Panics
    ///
    /// This function panics if `radix` is not in the range from 2 to 36.
    ///
    /// See [`u128::from_str_radix`].
    #[inline]
    pub const fn from_str_radix(src: &str, radix: u32) -> Result<Self, ParseIntError> {
        from_str_radix(src, radix)
    }
}

impl u256 {
    /// Create a new `u256` from the low and high bits.
    #[inline(always)]
    pub const fn new(lo: u128, hi: u128) -> Self {
        if cfg!(target_endian = "big") {
            Self::from_be_bytes(math::to_flat_bytes(hi.to_be_bytes(), lo.to_be_bytes()))
        } else {
            Self::from_le_bytes(math::to_flat_bytes(lo.to_le_bytes(), hi.to_le_bytes()))
        }
    }

    /// Get the high 128 bits of the signed integer.
    #[inline(always)]
    pub const fn high(self) -> u128 {
        if cfg!(target_endian = "big") {
            let (hi, _) = math::from_flat_bytes(self.to_be_bytes());
            u128::from_be_bytes(hi)
        } else {
            let (_, hi) = math::from_flat_bytes(self.to_le_bytes());
            u128::from_le_bytes(hi)
        }
    }

    /// Get the low 128 bits of the signed integer.
    #[inline(always)]
    pub const fn low(self) -> u128 {
        if cfg!(target_endian = "big") {
            let (_, lo) = math::from_flat_bytes(self.to_be_bytes());
            u128::from_be_bytes(lo)
        } else {
            let (lo, _) = math::from_flat_bytes(self.to_le_bytes());
            u128::from_le_bytes(lo)
        }
    }

    /// Get if the integer is even.
    #[inline(always)]
    pub const fn is_even(self) -> bool {
        self.low() % 2 == 0
    }

    /// Get if the integer is off.
    #[inline(always)]
    pub const fn is_off(self) -> bool {
        !self.is_even()
    }

    /// Create the 256-bit unsigned integer to a `u8`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u8(value: u8) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit unsigned integer from a `u16`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u16(value: u16) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit unsigned integer from a `u32`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u32(value: u32) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit unsigned integer from a `u64`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_u64(value: u64) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit unsigned integer from a `u128`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_u128(value: u128) -> Self {
        let (lo, hi) = math::as_uwide_u128(value);
        Self::new(lo, hi)
    }

    /// Create the 256-bit unsigned integer from an unsigned limb, as if by an
    /// `as` cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn from_ulimb(value: ULimb) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit unsigned integer from an unsigned wide type, as if by
    /// an `as` cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn from_uwide(value: UWide) -> Self {
        Self::from_u128(value as u128)
    }

    /// Create the 256-bit unsigned integer to an `i8`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_i8(value: i8) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit unsigned integer from an `i16`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_i16(value: i16) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit unsigned integer from an `i32`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_i32(value: i32) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit unsigned integer from an `i64`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_i64(value: i64) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit unsigned integer from an `i128`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_i128(value: i128) -> Self {
        let (lo, hi) = math::as_iwide_u128(value);
        Self::new(lo, hi)
    }

    /// Create the 256-bit unsigned integer from an `i256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_i256(value: i256) -> Self {
        value.as_u256()
    }

    /// Create the 256-bit unsigned integer from a signed limb, as if by an `as`
    /// cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn from_ilimb(value: ILimb) -> Self {
        Self::from_i128(value as i128)
    }

    /// Create the 256-bit unsigned integer from a signed wide type, as if by an
    /// `as` cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn from_iwide(value: IWide) -> Self {
        Self::from_i128(value as i128)
    }

    /// Convert the 256-bit unsigned integer to an `u8`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u8(&self) -> u8 {
        self.low() as u8
    }

    /// Convert the 256-bit unsigned integer to an `u16`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u16(&self) -> u16 {
        self.low() as u16
    }

    /// Convert the 256-bit unsigned integer to an `u32`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u32(&self) -> u32 {
        self.low() as u32
    }

    /// Convert the 256-bit unsigned integer to an `u64`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_u64(&self) -> u64 {
        self.low() as u64
    }

    /// Convert the 256-bit unsigned integer to an `u128`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_u128(&self) -> u128 {
        math::as_unarrow_u128(self.low(), self.high())
    }

    /// Convert the 256-bit unsigned integer to an `u256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_u256(&self) -> Self {
        *self
    }

    /// Convert the 256-bit unsigned integer to an unsigned limb, as if by an
    /// `as` cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn as_ulimb(&self) -> ULimb {
        self.as_u128() as ULimb
    }

    /// Convert the 256-bit unsigned integer to an unsigned wide type, as if by
    /// an `as` cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn as_uwide(&self) -> UWide {
        self.as_u128() as UWide
    }

    /// Convert the 256-bit unsigned integer to an `i8`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i8(&self) -> i8 {
        self.as_i128() as i8
    }

    /// Convert the 256-bit unsigned integer to an `i16`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i16(&self) -> i16 {
        self.as_i128() as i16
    }

    /// Convert the 256-bit unsigned integer to an `i32`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i32(&self) -> i32 {
        self.as_i128() as i32
    }

    /// Convert the 256-bit unsigned integer to an `i64`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_i64(&self) -> i64 {
        self.as_i128() as i64
    }

    /// Convert the 256-bit unsigned integer to an `i128`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_i128(&self) -> i128 {
        math::as_inarrow_u128(self.low(), self.high())
    }

    /// Convert the 256-bit unsigned integer to an `i256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_i256(&self) -> i256 {
        let (lo, hi) = math::wide_cast_u128(self.low(), self.high());
        i256::new(lo, hi)
    }

    /// Convert the 256-bit unsigned integer to a signed limb, as if by an `as`
    /// cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn as_ilimb(&self) -> ILimb {
        self.as_i128() as ILimb
    }

    /// Convert the 256-bit unsigned integer to a signed wide type, as if by an
    /// `as` cast.
    #[inline(always)]
    #[allow(clippy::unnecessary_cast)]
    pub const fn as_iwide(&self) -> IWide {
        self.as_i128() as IWide
    }

    /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn add_uwide(self, n: UWide) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_add_uwide(n)
        } else {
            match self.checked_add_uwide(n) {
                Some(v) => v,
                None => panic!("attempt to add with overflow"),
            }
        }
    }

    /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn wrapping_add_uwide(self, n: UWide) -> Self {
        let (lo, hi) = math::wrapping_add_wide_u128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn overflowing_add_uwide(self, n: UWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_add_wide_u128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn checked_add_uwide(self, n: UWide) -> Option<Self> {
        let (value, overflowed) = self.overflowing_add_uwide(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn sub_uwide(self, n: UWide) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_sub_uwide(n)
        } else {
            match self.checked_sub_uwide(n) {
                Some(v) => v,
                None => panic!("attempt to subtract with overflow"),
            }
        }
    }

    /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn wrapping_sub_uwide(self, n: UWide) -> Self {
        let (lo, hi) = math::wrapping_sub_wide_u128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn overflowing_sub_uwide(self, n: UWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_sub_wide_u128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn checked_sub_uwide(self, n: UWide) -> Option<Self> {
        let (value, overflowed) = self.overflowing_sub_uwide(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn mul_uwide(self, n: UWide) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_mul_uwide(n)
        } else {
            match self.checked_mul_uwide(n) {
                Some(v) => v,
                None => panic!("attempt to multiply with overflow"),
            }
        }
    }

    /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    ///
    /// Many different algorithms were attempted, with a soft [`mulx`] approach
    /// (1), a flat, fixed-width long multiplication (2), and a
    /// short-circuiting long multiplication (3). Algorithm (3) had the best
    /// performance for 128-bit multiplication, however, algorithm (1) was
    /// better for smaller type sizes.
    ///
    /// This also optimized much better when multiplying by a single or a
    /// half-sized item: rather than using 4 limbs, if we're multiplying
    /// `(u128, u128) * u128`, we can use 2 limbs for the right operand, and
    /// for `(u128, u128) * u64`, only 1 limb.
    ///
    /// # Assembly
    ///
    /// Using algorithm (3), the addition of `(u128, u128) + (u128, u128)` is in
    /// the worst case 10 `mul` and 15 `add` instructions, while `(u128,
    /// u128) + u128` is at worst 8 `mul` and 12 `add` instructions, which
    /// optimizes quite nicely.
    ///
    /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
    #[inline(always)]
    pub const fn wrapping_mul_uwide(self, n: UWide) -> Self {
        // 256-Bit
        // -------
        // wrapping_mul:
        //     push    r15
        //     push    r14
        //     push    r12
        //     push    rbx
        //     mov     r14, rdx
        //     mov     r11, qword ptr [rsp + 48]
        //     mov     rbx, qword ptr [rsp + 40]
        //     test    rsi, rsi
        //     je      .LBB1_1
        //     mov     rax, rbx
        //     mul     rsi
        //     mov     r12, rdx
        //     mov     r15, rax
        //     mov     rax, r11
        //     mul     rsi
        //     mov     r10, rdx
        //     mov     r9, rax
        //     add     r9, r12
        //     adc     r10, 0
        //     test    r14, r14
        //     jne     .LBB1_5
        // .LBB1_4:
        //     xor     r14d, r14d
        //     test    rcx, rcx
        //     jne     .LBB1_7
        //     jmp     .LBB1_8
        // .LBB1_1:
        //     xor     r9d, r9d
        //     xor     r15d, r15d
        //     xor     r10d, r10d
        //     test    r14, r14
        //     je      .LBB1_4
        // .LBB1_5:
        //     mov     rax, rbx
        //     mul     r14
        //     mov     rsi, rdx
        //     add     r9, rax
        //     adc     rsi, 0
        //     mov     rax, r11
        //     mul     r14
        //     mov     r14, rdx
        //     add     rax, rsi
        //     adc     r14, 0
        //     add     r10, rax
        //     adc     r14, 0
        //     test    rcx, rcx
        //     je      .LBB1_8
        // .LBB1_7:
        //     mov     rax, rbx
        //     mul     rcx
        //     imul    r11, rcx
        //     add     r10, rax
        //     adc     r11, rdx
        //     add     r14, r11
        // .LBB1_8:
        //     test    r8, r8
        //     je      .LBB1_10
        //     imul    r8, rbx
        //     add     r14, r8
        // .LBB1_10:
        //     mov     qword ptr [rdi + 8], r9
        //     mov     qword ptr [rdi], r15
        //     mov     qword ptr [rdi + 24], r14
        //     mov     qword ptr [rdi + 16], r10
        //     mov     rax, rdi
        //     pop     rbx
        //     pop     r12
        //     pop     r14
        //     pop     r15
        //     ret
        let n = math::split!(UWide, ULimb, n);
        let r = math::wrapping_mul_arr_u128(&self.to_le_limbs(), &n);
        Self::from_le_limbs(r)
    }

    /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    ///
    /// Many different algorithms were attempted, with a soft [`mulx`] approach
    /// (1), a flat, fixed-width long multiplication (2), and a
    /// short-circuiting long multiplication (3). Algorithm (3) had the best
    /// performance for 128-bit multiplication, however, algorithm (1) was
    /// better for smaller type sizes.
    ///
    /// This also optimized much better when multiplying by a single or a
    /// half-sized item: rather than using 4 limbs, if we're multiplying
    /// `(u128, u128) * u128`, we can use 2 limbs for the right operand, and
    /// for `(u128, u128) * u64`, only 1 limb.
    ///
    /// # Assembly
    ///
    /// The analysis here is practically identical to that of
    /// [`wrapping_mul_uwide`].
    ///
    /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
    /// [`wrapping_mul_uwide`]: Self::wrapping_mul_uwide
    #[inline(always)]
    pub const fn overflowing_mul_uwide(self, n: UWide) -> (Self, bool) {
        let n = math::split!(UWide, ULimb, n);
        let (r, overflow) = math::overflowing_mul_arr_u128(&self.to_le_limbs(), &n);
        (Self::from_le_limbs(r), overflow)
    }

    /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn checked_mul_uwide(self, n: UWide) -> Option<Self> {
        let (value, overflowed) = self.overflowing_mul_uwide(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Multiply the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn mul_ulimb(self, n: ULimb) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_mul_ulimb(n)
        } else {
            match self.checked_mul_ulimb(n) {
                Some(v) => v,
                None => panic!("attempt to multiply with overflow"),
            }
        }
    }

    /// Multiply the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    ///
    /// Many different algorithms were attempted, with a soft [`mulx`] approach
    /// (1), a flat, fixed-width long multiplication (2), and a
    /// short-circuiting long multiplication (3). Algorithm (3) had the best
    /// performance for 128-bit multiplication, however, algorithm (1) was
    /// better for smaller type sizes.
    ///
    /// This also optimized much better when multiplying by a single or a
    /// half-sized item: rather than using 4 limbs, if we're multiplying
    /// `(u128, u128) * u128`, we can use 2 limbs for the right operand, and
    /// for `(u128, u128) * u64`, only 1 limb.
    ///
    /// Using algorithm (3), the addition of `(u128, u128) + (u128, u128)` is in
    /// the worst case 10 `mul` and 15 `add` instructions, while `(u128,
    /// u128) + u64` is always 4 `mul` and 3 `add` instructions without any
    /// branching. This is extremely efficient.
    ///
    /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
    #[inline(always)]
    pub const fn wrapping_mul_ulimb(self, n: ULimb) -> Self {
        // 256-Bit
        // -------
        // wrapping_mul:
        //     push    rbx
        //     mov     rax, rcx
        //     mov     rcx, rdx
        //     imul    r8, r9
        //     mul     r9
        //     mov     r10, rdx
        //     mov     r11, rax
        //     mov     rax, rcx
        //     mul     r9
        //     mov     rcx, rdx
        //     mov     rbx, rax
        //     mov     rax, rsi
        //     mul     r9
        //     add     rdx, rbx
        //     adc     rcx, r11
        //     adc     r10, r8
        //     mov     qword ptr [rdi], rax
        //     mov     qword ptr [rdi + 8], rdx
        //     mov     qword ptr [rdi + 16], rcx
        //     mov     qword ptr [rdi + 24], r10
        //     mov     rax, rdi
        //     pop     rbx
        //     ret
        let r = math::wrapping_mul_arr_u128(&self.to_le_limbs(), &[n]);
        Self::from_le_limbs(r)
    }

    /// Multiply the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// Many different algorithms were attempted, with a soft [`mulx`] approach
    /// (1), a flat, fixed-width long multiplication (2), and a
    /// short-circuiting long multiplication (3). Algorithm (3) had the best
    /// performance for 128-bit multiplication, however, algorithm (1) was
    /// better for smaller type sizes.
    ///
    /// This also optimized much better when multiplying by a single or a
    /// half-sized item: rather than using 4 limbs, if we're multiplying
    /// `(u128, u128) * u128`, we can use 2 limbs for the right operand, and
    /// for `(u128, u128) * u64`, only 1 limb.
    ///
    /// # Assembly
    ///
    /// The analysis here is practically identical to that of
    /// [`wrapping_mul_ulimb`].
    ///
    /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
    /// [`wrapping_mul_ulimb`]: Self::wrapping_mul_ulimb
    #[inline(always)]
    pub const fn overflowing_mul_ulimb(self, n: ULimb) -> (Self, bool) {
        let (r, overflow) = math::overflowing_mul_arr_u128(&self.to_le_limbs(), &[n]);
        (Self::from_le_limbs(r), overflow)
    }

    /// Multiply the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full multiplication cannot do.
    #[inline(always)]
    pub const fn checked_mul_ulimb(self, n: ULimb) -> Option<Self> {
        let (value, overflowed) = self.overflowing_mul_ulimb(n);
        if overflowed {
            None
        } else {
            Some(value)
        }
    }

    /// Div/Rem operation on a 256-bit integer.
    ///
    /// This allows storing of both the quotient and remainder without
    /// making repeated calls.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    #[inline(always)]
    pub fn div_rem(self, n: Self) -> (Self, Self) {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div_rem(n)
        } else {
            self.checked_div_rem(n).expect("attempt to divide with overflow")
        }
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
        let x = self.to_le_limbs();
        let y = n.to_le_limbs();

        let (div, rem) = math::div_rem_full(&x, &y);
        let div = Self::from_le_limbs(div);
        let rem = Self::from_le_limbs(rem);

        (div, rem)
    }

    /// Div/Rem operation on a 256-bit integer.
    ///
    /// This allows storing of both the quotient and remainder without
    /// making repeated calls.
    #[inline(always)]
    pub fn checked_div_rem(self, n: Self) -> Option<(Self, Self)> {
        if n == Self::from_u8(0) {
            None
        } else {
            Some(self.wrapping_div_rem(n))
        }
    }

    /// Div/Rem operation on a 256-bit integer.
    ///
    /// This allows storing of both the quotient and remainder without
    /// making repeated calls.
    #[inline(always)]
    pub fn overflowing_div_rem(self, n: Self) -> ((Self, Self), bool) {
        if n == Self::from_u8(0) {
            ((Self::MAX, Self::from_u8(0)), true)
        } else {
            (self.wrapping_div_rem(n), false)
        }
    }

    /// Div/Rem the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`div_rem`]
    /// or [`div_rem_ulimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`div_rem`]: Self::div_rem
    /// [`div_rem_ulimb`]: Self::div_rem_ulimb
    #[inline(always)]
    pub fn div_rem_uwide(self, n: UWide) -> (Self, UWide) {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div_rem_uwide(n)
        } else {
            self.checked_div_rem_uwide(n).expect("attempt to divide with overflow")
        }
    }

    /// Div/Rem the 256-bit integer by a wide, 128-bit unsigned factor.
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
    #[inline(always)]
    pub fn wrapping_div_rem_uwide(self, n: UWide) -> (Self, UWide) {
        let x = self.to_le_limbs();
        let (div, rem) = math::div_rem_wide(&x, n);
        let div = u256::from_le_limbs(div);
        (div, rem)
    }

    /// Div/Rem the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`checked_div_rem`]
    /// or [`checked_div_rem_ulimb`] if possible.
    ///
    /// [`checked_div_rem`]: Self::checked_div_rem
    /// [`checked_div_rem_ulimb`]: Self::checked_div_rem_ulimb
    #[inline(always)]
    pub fn checked_div_rem_uwide(self, n: UWide) -> Option<(Self, UWide)> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_div_rem_uwide(n))
        }
    }

    /// Div/Rem the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`overflowing_div_rem`]
    /// or [`overflowing_div_rem_ulimb`] if possible.
    ///
    /// [`overflowing_div_rem`]: Self::overflowing_div_rem
    /// [`overflowing_div_rem_ulimb`]: Self::overflowing_div_rem_ulimb
    #[inline(always)]
    pub fn overflowing_div_rem_uwide(self, n: UWide) -> ((Self, UWide), bool) {
        if n == 0 {
            ((Self::MAX, 0), true)
        } else {
            (self.wrapping_div_rem_uwide(n), false)
        }
    }

    /// Div the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`div`]
    /// or [`div_ulimb`] if possible.
    ///
    /// [`div`]: Self::div
    /// [`div_ulimb`]: Self::div_ulimb
    #[inline(always)]
    pub fn div_uwide(self, n: UWide) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.div_rem_uwide(n).0
        } else {
            self.checked_div_uwide(n).expect("attempt to divide by zero")
        }
    }

    /// Div the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`wrapping_div`]
    /// or [`wrapping_div_ulimb`] if possible.
    ///
    /// [`wrapping_div`]: Self::wrapping_div
    /// [`wrapping_div_ulimb`]: Self::wrapping_div_ulimb
    #[inline(always)]
    pub fn wrapping_div_uwide(self, n: UWide) -> Self {
        self.wrapping_div_rem_uwide(n).0
    }

    /// Div the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    /// Performance of this is highly variable: for small
    /// divisors it can be very fast, for larger divisors
    /// due to the creation of the temporary divisor it
    /// can be significantly slower.
    #[inline(always)]
    pub fn overflowing_div_uwide(self, n: UWide) -> (Self, bool) {
        let (divrem, overflow) = self.overflowing_div_rem_uwide(n);
        (divrem.0, overflow)
    }

    /// Div the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`checked_div`]
    /// or [`checked_div_ulimb`] if possible.
    ///
    /// [`checked_div`]: Self::checked_div
    /// [`checked_div_ulimb`]: Self::checked_div_ulimb
    #[inline(always)]
    pub fn checked_div_uwide(self, n: UWide) -> Option<Self> {
        Some(self.checked_div_rem_uwide(n)?.0)
    }

    /// Rem the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`rem`]
    /// or [`rem_ulimb`] if possible.
    ///
    /// [`rem`]: Self::rem
    /// [`rem_ulimb`]: Self::rem_ulimb
    #[inline(always)]
    pub fn rem_uwide(self, n: UWide) -> UWide {
        if cfg!(not(have_overflow_checks)) {
            self.div_rem_uwide(n).1
        } else {
            self.checked_rem_uwide(n).expect("attempt to divide by zero")
        }
    }

    /// Rem the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`wrapping_rem`]
    /// or [`wrapping_rem_ulimb`] if possible.
    ///
    /// [`wrapping_rem`]: Self::wrapping_rem
    /// [`wrapping_rem_ulimb`]: Self::wrapping_rem_ulimb
    #[inline(always)]
    pub fn wrapping_rem_uwide(self, n: UWide) -> UWide {
        self.wrapping_div_rem_uwide(n).1
    }

    /// Div the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`overflowing_rem`]
    /// or [`overflowing_rem_ulimb`] if possible.
    ///
    /// [`overflowing_rem`]: Self::overflowing_rem
    /// [`overflowing_rem_ulimb`]: Self::overflowing_rem_ulimb
    #[inline(always)]
    pub fn overflowing_rem_uwide(self, n: UWide) -> (UWide, bool) {
        let (divrem, overflow) = self.overflowing_div_rem_uwide(n);
        (divrem.1, overflow)
    }

    /// Div the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`checked_rem`]
    /// or [`checked_rem_ulimb`] if possible.
    ///
    /// [`checked_rem`]: Self::checked_rem
    /// [`checked_rem_ulimb`]: Self::checked_rem_ulimb
    #[inline(always)]
    pub fn checked_rem_uwide(self, n: UWide) -> Option<UWide> {
        Some(self.checked_div_rem_uwide(n)?.1)
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    #[inline(always)]
    pub fn div_rem_ulimb(self, n: ULimb) -> (Self, ULimb) {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div_rem_ulimb(n)
        } else {
            self.checked_div_rem_ulimb(n).expect("attempt to divide with overflow")
        }
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    #[inline(always)]
    pub fn wrapping_div_rem_ulimb(self, n: ULimb) -> (Self, ULimb) {
        let x = self.to_le_limbs();
        let (div, rem) = math::div_rem_limb(&x, n);
        let div = u256::from_le_limbs(div);
        (div, rem)
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_div_rem_ulimb(self, n: ULimb) -> Option<(Self, ULimb)> {
        if n == 0 {
            None
        } else {
            Some(self.wrapping_div_rem_ulimb(n))
        }
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_div_rem_ulimb(self, n: ULimb) -> ((Self, ULimb), bool) {
        if n == 0 {
            ((Self::MAX, 0), true)
        } else {
            (self.wrapping_div_rem_ulimb(n), false)
        }
    }

    /// Div the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn div_ulimb(self, n: ULimb) -> Self {
        if cfg!(not(have_overflow_checks)) {
            self.div_rem_ulimb(n).0
        } else {
            self.checked_div_ulimb(n).expect("attempt to divide by zero")
        }
    }

    /// Div the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn wrapping_div_ulimb(self, n: ULimb) -> Self {
        self.wrapping_div_rem_ulimb(n).0
    }

    /// Div the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_div_ulimb(self, n: ULimb) -> (Self, bool) {
        let (divrem, overflow) = self.overflowing_div_rem_ulimb(n);
        (divrem.0, overflow)
    }

    /// Div the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_div_ulimb(self, n: ULimb) -> Option<Self> {
        Some(self.checked_div_rem_ulimb(n)?.0)
    }

    /// Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn rem_ulimb(self, n: ULimb) -> ULimb {
        if cfg!(not(have_overflow_checks)) {
            self.div_rem_ulimb(n).1
        } else {
            self.checked_rem_ulimb(n).expect("attempt to divide by zero")
        }
    }

    /// Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn wrapping_rem_ulimb(self, n: ULimb) -> ULimb {
        self.wrapping_div_rem_ulimb(n).1
    }

    /// Div the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn overflowing_rem_ulimb(self, n: ULimb) -> (ULimb, bool) {
        let (divrem, overflow) = self.overflowing_div_rem_ulimb(n);
        (divrem.1, overflow)
    }

    /// Div the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    #[inline(always)]
    pub fn checked_rem_ulimb(self, n: ULimb) -> Option<ULimb> {
        Some(self.checked_div_rem_ulimb(n)?.1)
    }
}

// These are implementations for nightly-only APIs.
impl u256 {
    /// Returns the bit pattern of `self` reinterpreted as a signed integer of
    /// the same size.
    ///
    /// This produces the same result as an `as` cast, but ensures that the
    /// bit-width remains the same.
    ///
    /// See [`u128::cast_signed`].
    #[inline(always)]
    pub const fn cast_signed(self) -> i256 {
        self.as_i256()
    }

    /// Calculates `self` + `rhs` + `carry` and returns a tuple containing
    /// the sum and the output carry.
    ///
    /// Performs "ternary addition" of two integer operands and a carry-in
    /// bit, and returns an output integer and a carry-out bit. This allows
    /// chaining together multiple additions to create a wider addition, and
    /// can be useful for bignum addition.
    ///
    /// See [`u128::carrying_add`].
    #[inline]
    #[must_use]
    pub const fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool) {
        let (a, b) = self.overflowing_add(rhs);
        let (c, d) = a.overflowing_add(Self::from_u8(carry as u8));
        (c, b | d)
    }

    /// Calculates `self` &minus; `rhs` &minus; `borrow` and returns a tuple
    /// containing the difference and the output borrow.
    ///
    /// Performs "ternary subtraction" by subtracting both an integer
    /// operand and a borrow-in bit from `self`, and returns an output
    /// integer and a borrow-out bit. This allows chaining together multiple
    /// subtractions to create a wider subtraction, and can be useful for
    /// bignum subtraction.
    ///
    /// See [`u128::borrowing_sub`].
    #[inline]
    #[must_use]
    pub const fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool) {
        let (a, b) = self.overflowing_sub(rhs);
        let (c, d) = a.overflowing_sub(Self::from_u8(borrow as u8));
        (c, b | d)
    }

    /// Calculates `self` - `rhs` with a signed `rhs`
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    #[inline]
    #[must_use]
    pub const fn overflowing_sub_signed(self, rhs: i256) -> (Self, bool) {
        let (res, overflow) = self.overflowing_sub(rhs.as_u256());
        (res, overflow ^ (rhs.is_negative()))
    }

    /// Strict integer addition. Computes `self + rhs`, panicking
    /// if overflow occurred.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`u128::strict_add`].
    #[inline]
    #[must_use]
    pub const fn strict_add(self, rhs: Self) -> Self {
        match self.checked_add(rhs) {
            Some(v) => v,
            None => panic!("attempt to add with overflow"),
        }
    }

    /// Strict addition with a signed integer. Computes `self + rhs`,
    /// panicking if overflow occurred.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`u128::strict_add_signed`].
    #[inline]
    #[must_use]
    pub const fn strict_add_signed(self, rhs: i256) -> Self {
        match self.checked_add_signed(rhs) {
            Some(v) => v,
            None => panic!("attempt to add with overflow"),
        }
    }

    /// Strict integer subtraction. Computes `self - rhs`, panicking if
    /// overflow occurred.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`u128::strict_sub`].
    #[inline]
    #[must_use]
    pub const fn strict_sub(self, rhs: Self) -> Self {
        match self.checked_sub(rhs) {
            Some(v) => v,
            None => panic!("attempt to subtract with overflow"),
        }
    }

    /// Strict integer multiplication. Computes `self * rhs`, panicking if
    /// overflow occurred.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`u128::strict_mul`].
    #[inline]
    #[must_use]
    pub const fn strict_mul(self, rhs: Self) -> Self {
        match self.checked_mul(rhs) {
            Some(v) => v,
            None => panic!("attempt to subtract with overflow"),
        }
    }

    /// Strict integer division. Computes `self / rhs`.
    ///
    /// Strict division on unsigned types is just normal division. There's no
    /// way overflow could ever happen. This function exists so that all
    /// operations are accounted for in the strict operations.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::strict_div`].
    #[must_use]
    #[inline(always)]
    pub fn strict_div(self, rhs: Self) -> Self {
        match self.checked_div(rhs) {
            Some(v) => v,
            None => panic!("attempt to divide by zero"),
        }
    }

    /// Strict integer remainder. Computes `self % rhs`.
    ///
    /// Strict remainder calculation on unsigned types is just the regular
    /// remainder calculation. There's no way overflow could ever happen.
    /// This function exists so that all operations are accounted for in the
    /// strict operations.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::strict_rem`].
    #[must_use]
    #[inline(always)]
    pub fn strict_rem(self, rhs: Self) -> Self {
        match self.checked_rem(rhs) {
            Some(v) => v,
            None => panic!("attempt to divide by zero"),
        }
    }

    /// Strict Euclidean division. Computes `self.div_euclid(rhs)`.
    ///
    /// Strict division on unsigned types is just normal division. There's no
    /// way overflow could ever happen. This function exists so that all
    /// operations are accounted for in the strict operations. Since, for the
    /// positive integers, all common definitions of division are equal, this
    /// is exactly equal to `self.strict_div(rhs)`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::strict_div_euclid`].
    #[must_use]
    #[inline(always)]
    pub fn strict_div_euclid(self, rhs: Self) -> Self {
        match self.checked_div_euclid(rhs) {
            Some(v) => v,
            None => panic!("attempt to divide by zero"),
        }
    }

    /// Strict Euclidean modulo. Computes `self.rem_euclid(rhs)`.
    ///
    /// Strict modulo calculation on unsigned types is just the regular
    /// remainder calculation. There's no way overflow could ever happen.
    /// This function exists so that all operations are accounted for in the
    /// strict operations. Since, for the positive integers, all common
    /// definitions of division are equal, this is exactly equal to
    /// `self.strict_rem(rhs)`.
    ///
    /// # Panics
    ///
    /// This function will panic if `rhs` is zero.
    ///
    /// See [`u128::strict_rem_euclid`].
    #[must_use]
    #[inline(always)]
    pub fn strict_rem_euclid(self, rhs: Self) -> Self {
        match self.checked_rem_euclid(rhs) {
            Some(v) => v,
            None => panic!("attempt to divide by zero"),
        }
    }

    /// Strict negation. Computes `-self`, panicking unless `self ==
    /// 0`.
    ///
    /// Note that negating any positive integer will overflow.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`u128::strict_neg`].
    #[inline]
    #[must_use]
    pub const fn strict_neg(self) -> Self {
        match self.checked_neg() {
            Some(v) => v,
            None => panic!("attempt to negate with overflow"),
        }
    }

    /// Strict shift left. Computes `self << rhs`, panicking if `rhs` is larger
    /// than or equal to the number of bits in `self`.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`u128::strict_shl`].
    #[inline]
    #[must_use]
    pub const fn strict_shl(self, rhs: u32) -> Self {
        match self.checked_shl(rhs) {
            Some(v) => v,
            None => panic!("attempt to shift left with overflow"),
        }
    }

    /// Strict shift right. Computes `self >> rhs`, panicking `rhs` is
    /// larger than or equal to the number of bits in `self`.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`u128::strict_shr`].
    #[inline]
    #[must_use]
    pub const fn strict_shr(self, rhs: u32) -> Self {
        match self.checked_shr(rhs) {
            Some(v) => v,
            None => panic!("attempt to shift right with overflow"),
        }
    }

    /// Strict exponentiation. Computes `self.pow(exp)`, panicking if
    /// overflow occurred.
    ///
    /// # Panics
    ///
    /// ## Overflow behavior
    ///
    /// This function will always panic on overflow, regardless of whether
    /// overflow checks are enabled.
    ///
    /// See [`u128::strict_pow`].
    #[inline]
    #[must_use]
    pub const fn strict_pow(self, rhs: u32) -> Self {
        match self.checked_pow(rhs) {
            Some(v) => v,
            None => panic!("attempt to multiply with overflow"),
        }
    }

    /// Calculates the middle point of `self` and `rhs`.
    ///
    /// `midpoint(a, b)` is `(a + b) / 2` as if it were performed in a
    /// sufficiently-large unsigned integral type. This implies that the result
    /// is always rounded towards zero and that no overflow will ever occur.
    ///
    /// See [`u128::midpoint`].
    #[inline]
    #[must_use]
    pub const fn midpoint(self, rhs: Self) -> Self {
        // Use the well known branchless algorithm from Hacker's Delight to compute
        // `(a + b) / 2` without overflowing: `((a ^ b) >> 1) + (a & b)`.
        let xor = bitxor(self, rhs);
        let (lo, hi) = math::shr_u128(xor.low(), xor.high(), 1);
        Self::new(lo, hi).wrapping_add(bitand(self, rhs))
    }

    /// Unchecked integer addition. Computes `self + rhs`, assuming overflow
    /// cannot occur.
    ///
    /// Calling `x.unchecked_add(y)` is semantically equivalent to calling
    /// `x.`[`checked_add`]`(y).`[`unwrap_unchecked`]`()`.
    ///
    /// If you're just trying to avoid the panic in debug mode, then **do not**
    /// use this.  Instead, you're looking for [`wrapping_add`].
    ///
    /// # Safety
    ///
    /// This results in undefined behavior when the value overflows.
    ///
    /// See [`u128::unchecked_add`].
    ///
    /// [`checked_add`]: Self::checked_add
    /// [`wrapping_add`]: Self::wrapping_add
    /// [`unwrap_unchecked`]: Option::unwrap_unchecked
    #[must_use]
    #[inline(always)]
    pub unsafe fn unchecked_add(self, rhs: Self) -> Self {
        match self.checked_add(rhs) {
            Some(value) => value,
            // SAFETY: this is guaranteed to be safe by the caller.
            None => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Unchecked integer subtraction. Computes `self - rhs`, assuming overflow
    /// cannot occur.
    ///
    /// Calling `x.unchecked_sub(y)` is semantically equivalent to calling
    /// `x.`[`checked_sub`]`(y).`[`unwrap_unchecked`]`()`.
    ///
    /// If you're just trying to avoid the panic in debug mode, then **do not**
    /// use this.  Instead, you're looking for [`wrapping_sub`].
    ///
    /// # Safety
    ///
    /// This results in undefined behavior when the value overflows.
    ///
    /// See [`u128::unchecked_sub`].
    ///
    /// [`checked_sub`]: Self::checked_sub
    /// [`wrapping_sub`]: Self::wrapping_sub
    /// [`unwrap_unchecked`]: Option::unwrap_unchecked
    #[must_use]
    #[inline(always)]
    pub unsafe fn unchecked_sub(self, rhs: Self) -> Self {
        match self.checked_sub(rhs) {
            Some(value) => value,
            // SAFETY: this is guaranteed to be safe by the caller.
            None => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Unchecked integer multiplication. Computes `self * rhs`, assuming
    /// overflow cannot occur.
    ///
    /// Calling `x.unchecked_mul(y)` is semantically equivalent to calling
    /// `x.`[`checked_mul`]`(y).`[`unwrap_unchecked`]`()`.
    ///
    /// If you're just trying to avoid the panic in debug mode, then **do not**
    /// use this.  Instead, you're looking for [`wrapping_mul`].
    ///
    /// # Safety
    ///
    /// This results in undefined behavior when the value overflows.
    ///
    /// See [`u128::unchecked_mul`].
    ///
    /// [`wrapping_mul`]: Self::wrapping_mul
    /// [`checked_mul`]: Self::checked_mul
    /// [`unwrap_unchecked`]: Option::unwrap_unchecked
    #[must_use]
    #[inline(always)]
    pub const unsafe fn unchecked_mul(self, rhs: Self) -> Self {
        match self.checked_mul(rhs) {
            Some(value) => value,
            // SAFETY: this is guaranteed to be safe by the caller.
            None => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Unchecked shift left. Computes `self << rhs`, assuming that
    /// `rhs` is less than the number of bits in `self`.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `rhs` is larger than
    /// or equal to the number of bits in `self`,
    /// i.e. when [`checked_shl`] would return `None`.
    ///
    /// See [`u128::unchecked_shl`].
    ///
    /// [`checked_shl`]: Self::checked_shl
    #[must_use]
    #[inline(always)]
    pub const unsafe fn unchecked_shl(self, rhs: u32) -> Self {
        match self.checked_shl(rhs) {
            Some(value) => value,
            // SAFETY: this is guaranteed to be safe by the caller.
            None => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Unchecked shift right. Computes `self >> rhs`, assuming that
    /// `rhs` is less than the number of bits in `self`.
    ///
    /// # Safety
    ///
    /// This results in undefined behavior if `rhs` is larger than
    /// or equal to the number of bits in `self`,
    /// i.e. when [`checked_shr`] would return `None`.
    ///
    /// See [`u128::unchecked_shr`].
    ///
    /// [`checked_shr`]: Self::checked_shr
    #[must_use]
    #[inline(always)]
    pub const unsafe fn unchecked_shr(self, rhs: u32) -> Self {
        match self.checked_shr(rhs) {
            Some(value) => value,
            // SAFETY: this is guaranteed to be safe by the caller.
            None => unsafe { core::hint::unreachable_unchecked() },
        }
    }

    /// Checked subtraction with a signed integer. Computes `self - rhs`,
    /// returning `None` if overflow occurred.
    #[inline]
    pub const fn checked_signed_diff(self, rhs: Self) -> Option<i256> {
        let res = self.wrapping_sub(rhs).as_i256();
        let overflow = ge(self, rhs) == i256_lt(res, i256::from_u8(0));

        if !overflow {
            Some(res)
        } else {
            None
        }
    }

    /// Unbounded shift left. Computes `self << rhs`, without bounding the value
    /// of `rhs`.
    ///
    /// If `rhs` is larger or equal to the number of bits in `self`,
    /// the entire value is shifted out, and `0` is returned.
    #[inline]
    #[must_use]
    pub const fn unbounded_shl(self, rhs: u32) -> Self {
        if rhs < Self::BITS {
            self.wrapping_shl(rhs)
        } else {
            Self::from_u8(0)
        }
    }

    /// Unbounded shift right. Computes `self >> rhs`, without bounding the
    /// value of `rhs`.
    ///
    /// If `rhs` is larger or equal to the number of bits in `self`,
    /// the entire value is shifted out, and `0` is returned.
    #[inline]
    #[must_use]
    pub const fn unbounded_shr(self, rhs: u32) -> Self {
        if rhs < Self::BITS {
            self.wrapping_shr(rhs)
        } else {
            Self::from_u8(0)
        }
    }
}

impl Add for u256 {
    type Output = Self;

    #[inline(always)]
    fn add(self, rhs: Self) -> Self::Output {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_add(rhs)
        } else {
            self.checked_add(rhs).expect("attempt to add with overflow")
        }
    }
}

op_impl!(u256, Add, AddAssign, add, add_assign);

impl fmt::Binary for u256 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        // NOTE: This works for binary, since the value as always divisible.
        if f.alternate() {
            write!(f, "{:#b}", self.high())?;
        } else {
            write!(f, "{:b}", self.high())?;
        }
        write!(f, "{:b}", self.low())
    }
}

impl BitAnd for u256 {
    type Output = Self;

    #[inline(always)]
    fn bitand(self, rhs: Self) -> Self::Output {
        bitand(self, rhs)
    }
}

op_impl!(u256, BitAnd, BitAndAssign, bitand, bitand_assign);

impl BitOr for u256 {
    type Output = u256;

    #[inline(always)]
    fn bitor(self, rhs: Self) -> Self::Output {
        bitor(self, rhs)
    }
}

op_impl!(u256, BitOr, BitOrAssign, bitor, bitor_assign);

impl BitXor for u256 {
    type Output = Self;

    #[inline(always)]
    fn bitxor(self, rhs: Self) -> Self::Output {
        bitxor(self, rhs)
    }
}

op_impl!(u256, BitXor, BitXorAssign, bitxor, bitxor_assign);

impl fmt::Debug for u256 {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        fmt::Display::fmt(self, f)
    }
}

impl fmt::Display for u256 {
    #[inline]
    #[allow(clippy::bind_instead_of_map)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if self.high() == 0 {
            return fmt::Display::fmt(&self.low(), f);
        }

        let mut buffer = [0u8; 78];
        let formatted = to_string(*self, &mut buffer).or_else(|_| Err(fmt::Error))?;
        write!(f, "{}", formatted)
    }
}

impl Div for u256 {
    type Output = Self;

    #[inline(always)]
    fn div(self, rhs: Self) -> Self::Output {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_div(rhs)
        } else {
            self.checked_div(rhs).expect("attempt to divide by zero")
        }
    }
}

op_impl!(u256, Div, DivAssign, div, div_assign);

impl From<bool> for u256 {
    #[inline(always)]
    fn from(small: bool) -> Self {
        Self::new(small as u128, 0)
    }
}

impl From<char> for u256 {
    #[inline(always)]
    fn from(c: char) -> Self {
        Self::new(c as u128, 0)
    }
}

from_impl!(u256, u8, from_u8);
from_impl!(u256, u16, from_u16);
from_impl!(u256, u32, from_u32);
from_impl!(u256, u64, from_u64);
from_impl!(u256, u128, from_u128);

impl FromStr for u256 {
    type Err = ParseIntError;

    /// Parses a string s to return a value of this type.
    ///
    /// This is not optimized, since all optimization is done in
    /// the lexical implementation.
    #[inline]
    fn from_str(src: &str) -> Result<u256, ParseIntError> {
        // up to 39 digits can be stored in a `u128`, so less is always valid
        // meanwhile, 78 is good for all 256-bit integers. 32-bit architectures
        // on average have poor support for 128-bit operations so we try to use `u64`.
        if (cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32"))
            && src.len() < 20
        {
            Ok(u256::from_u64(u64::from_str(src)?))
        } else if src.len() < 39 {
            Ok(u256::from_u128(u128::from_str(src)?))
        } else {
            u256::from_str_radix(src, 10)
        }
    }
}

impl fmt::LowerExp for u256 {
    #[inline]
    #[allow(clippy::bind_instead_of_map)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if self.high() == 0 {
            return fmt::LowerExp::fmt(&self.low(), f);
        }

        let mut buffer = [0u8; 78];
        let buffer = to_bytes(*self, &mut buffer);
        let first = buffer[0] as char;
        let formatted = str::from_utf8(&buffer[1..]).or_else(|_| Err(fmt::Error))?;
        write!(f, "{}.{}e{}", first, formatted, buffer.len() - 1)
    }
}

impl fmt::LowerHex for u256 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        // NOTE: This works for hex, since the value as always divisible.
        if f.alternate() {
            write!(f, "{:#x}", self.high())?;
        } else {
            write!(f, "{:x}", self.high())?;
        }
        write!(f, "{:x}", self.low())
    }
}

impl Mul for u256 {
    type Output = u256;

    #[inline(always)]
    fn mul(self, rhs: Self) -> Self::Output {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_mul(rhs)
        } else {
            self.checked_mul(rhs).expect("attempt to multiply with overflow")
        }
    }
}

op_impl!(u256, Mul, MulAssign, mul, mul_assign);

impl Not for u256 {
    type Output = u256;

    #[inline(always)]
    fn not(self) -> Self::Output {
        not(self)
    }
}

ref_impl!(u256, Not, not);

impl fmt::Octal for u256 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        // NOTE: This is **NOT** divisible by 8, so `log(128, 8)` is not integral.
        // So, we can break it into pairs of u64.
        let hi1 = (self.high() >> 64) as u64;
        let hi0 = self.high() as u64;
        let lo1 = (self.low() >> 64) as u64;
        let lo0 = self.low() as u64;

        let alternate = f.alternate();
        let mut write = |x: u64, alt: bool| {
            if alt {
                write!(f, "{:#o}", x)
            } else {
                write!(f, "{:o}", x)
            }
        };
        if hi1 != 0 {
            write(hi1, alternate)?;
            write(hi0, false)?;
            write(lo1, false)?;
            write(lo0, false)
        } else if hi0 != 0 {
            write(hi0, alternate)?;
            write(lo1, false)?;
            write(lo0, false)
        } else if lo1 != 0 {
            write(lo1, alternate)?;
            write(lo0, false)
        } else {
            // NOTE: Always write at least a 0
            write(lo0, alternate)
        }
    }
}

impl Ord for u256 {
    #[inline(always)]
    fn cmp(&self, other: &Self) -> Ordering {
        cmp(*self, *other)
    }
}

impl PartialOrd for u256 {
    #[inline(always)]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }

    #[inline(always)]
    fn lt(&self, other: &Self) -> bool {
        lt(*self, *other)
    }

    #[inline(always)]
    fn le(&self, other: &Self) -> bool {
        le(*self, *other)
    }

    #[inline(always)]
    fn gt(&self, other: &Self) -> bool {
        gt(*self, *other)
    }

    #[inline(always)]
    fn ge(&self, other: &Self) -> bool {
        ge(*self, *other)
    }
}

impl Rem for u256 {
    type Output = u256;

    #[inline(always)]
    fn rem(self, rhs: Self) -> Self::Output {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_rem(rhs)
        } else {
            self.checked_rem(rhs)
                .expect("attempt to calculate the remainder with a divisor of zero")
        }
    }
}

op_impl!(u256, Rem, RemAssign, rem, rem_assign);

macro_rules! shift_const_impl {
    (@shl $value:ident, $shift:ident) => {{
        let (lo, hi) = math::shl_u128($value.low(), $value.high(), $shift as u32);
        Self::new(lo, hi)
    }};

    (@shr $value:ident, $shift:ident) => {{
        let (lo, hi) = math::shr_u128($value.low(), $value.high(), $shift as u32);
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
            let max = Self::from_u16(256);
            let other = other.as_u256();
            debug_assert!(lt(other, max), "attempt to shift left with overflow");
            let shift = (other.low() & (u32::MAX as u128)) as u32;
            shift_const_impl!(@shl self, shift)
        }

        /// Const evaluation of shr.
        ///
        /// This behavior is wrapping: if `other >= 256`, this wraps.
        pub const fn $shr(self, other: $t) -> Self {
            let max = Self::from_u16(256);
            let other = other.as_u256();
            debug_assert!(lt(other, max), "attempt to shift right with overflow");
            let shift = other.low() & (u32::MAX as u128);
            shift_const_impl!(@shr self, shift)
        }
    );
}

// Const implementations for Shl
impl u256 {
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

impl Shl for u256 {
    type Output = Self;

    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shl(self, other: Self) -> Self::Output {
        let shift = other.low() & (u32::MAX as u128);
        shift_const_impl!(@shl self, shift)
    }
}

ref_impl!(u256, Shl, shl, other: &u256);
ref_t_impl!(u256, Shl, shl);

impl Shr for u256 {
    type Output = Self;

    #[inline(always)]
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn shr(self, other: Self) -> Self::Output {
        let shift = other.low() & (u32::MAX as u128);
        shift_const_impl!(@shr self, shift)
    }
}

ref_impl!(u256, Shr, shr, other: &u256);
ref_t_impl!(u256, Shr, shr);

macro_rules! shift_impl {
    (@mod $($t:ty)*) => ($(
        impl Shl<$t> for u256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shl(self, other: $t) -> Self::Output {
                let shift = other % 256;
                shift_const_impl!(@shl self, shift)
            }
        }

        impl Shr<$t> for u256 {
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
        impl Shl<$t> for u256 {
            type Output = Self;

            #[inline(always)]
            fn shl(self, other: $t) -> Self::Output {
                shift_const_impl!(@shl self, other)
            }
        }

        impl Shr<$t> for u256 {
            type Output = Self;

            #[inline(always)]
            fn shr(self, other: $t) -> Self::Output {
                shift_const_impl!(@shr self, other)
            }
        }
    )*);

    (@256 $($t:ty)*) => ($(
        impl Shl<$t> for u256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shl(self, other: $t) -> Self::Output {
                let shift = other % i256::from_u16(256);
                let shift = shift.as_u32();
                shift_const_impl!(@shl self, shift)
            }
        }

        impl Shr<$t> for u256 {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shr(self, other: $t) -> Self::Output {
                let shift = other % i256::from_u16(256);
                let shift = shift.as_u32();
                shift_const_impl!(@shr self, shift)
            }
        }
    )*);

    ($($t:ty)*) => ($(
        impl Shl<&$t> for u256 {
            type Output = <Self as Shl>::Output;

            #[inline(always)]
            fn shl(self, other: &$t) -> Self::Output {
                self.shl(*other)
            }
        }

        impl ShlAssign<$t> for u256 {
            #[inline(always)]
            fn shl_assign(&mut self, other: $t) {
                *self = self.shl(other);
            }
        }

        impl ShlAssign<&$t> for u256 {
            #[inline(always)]
            fn shl_assign(&mut self, other: &$t) {
                *self = self.shl(other);
            }
        }

        impl Shr<&$t> for u256 {
            type Output = <Self as Shr>::Output;

            #[inline(always)]
            fn shr(self, other: &$t) -> Self::Output {
                self.shr(*other)
            }
        }

        impl ShrAssign<$t> for u256 {
            #[inline(always)]
            fn shr_assign(&mut self, other: $t) {
                *self = self.shr(other);
            }
        }

        impl ShrAssign<&$t> for u256 {
            #[inline(always)]
            fn shr_assign(&mut self, other: &$t) {
                *self = self.shr(other);
            }
        }
    )*);
}

shift_impl! { @nomod i8 u8 }
shift_impl! { @mod i16 i32 i64 i128 isize u16 u32 u64 u128 usize }
shift_impl! { @256 i256 }
shift_impl! { i8 i16 i32 i64 i128 i256 isize u8 u16 u32 u64 u128 usize }

impl Sub for u256 {
    type Output = u256;

    #[inline(always)]
    fn sub(self, rhs: Self) -> Self::Output {
        if cfg!(not(have_overflow_checks)) {
            self.wrapping_sub(rhs)
        } else {
            self.checked_sub(rhs).expect("attempt to subtract with overflow")
        }
    }
}

op_impl!(u256, Sub, SubAssign, sub, sub_assign);

macro_rules! try_from_impl {
    ($($t:ty)*) => ($(
        impl TryFrom<$t> for u256 {
            type Error = TryFromIntError;

            #[inline(always)]
            fn try_from(u: $t) -> Result<Self, TryFromIntError> {
                if u >= 0 {
                    Ok(Self::from_u128(u as u128))
                } else {
                    Err(TryFromIntError {})
                }
            }
        }
    )*);
}

try_from_impl! { i8 i16 i32 i64 i128 isize }

impl TryFrom<i256> for u256 {
    type Error = TryFromIntError;

    #[inline(always)]
    fn try_from(u: i256) -> Result<Self, TryFromIntError> {
        if u.high() >= 0 {
            Ok(u.as_u256())
        } else {
            Err(TryFromIntError {})
        }
    }
}

impl fmt::UpperExp for u256 {
    #[inline]
    #[allow(clippy::bind_instead_of_map)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        if self.high() == 0 {
            return fmt::UpperExp::fmt(&self.low(), f);
        }

        let mut buffer: [u8; 78] = [0u8; 78];
        let buffer = to_bytes(*self, &mut buffer);
        let first = buffer[0] as char;
        let formatted = str::from_utf8(&buffer[1..]).or_else(|_| Err(fmt::Error))?;
        write!(f, "{}.{}E{}", first, formatted, buffer.len() - 1)
    }
}

impl fmt::UpperHex for u256 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> Result<(), fmt::Error> {
        // NOTE: This works for hex, since the value as always divisible.
        if f.alternate() {
            write!(f, "{:#X}", self.high())?;
        } else {
            write!(f, "{:X}", self.high())?;
        }
        write!(f, "{:X}", self.low())
    }
}

/// Const implementation of `BitAnd` for internal algorithm use.
#[inline(always)]
const fn bitand(lhs: u256, rhs: u256) -> u256 {
    u256::new(lhs.low() & rhs.low(), lhs.high() & rhs.high())
}

/// Const implementation of `BitOr` for internal algorithm use.
#[inline(always)]
const fn bitor(lhs: u256, rhs: u256) -> u256 {
    u256::new(lhs.low() | rhs.low(), lhs.high() | rhs.high())
}

/// Const implementation of `BitXor` for internal algorithm use.
#[inline(always)]
const fn bitxor(lhs: u256, rhs: u256) -> u256 {
    u256::new(lhs.low() ^ rhs.low(), lhs.high() ^ rhs.high())
}

/// Const implementation of `Not` for internal algorithm use.
#[inline(always)]
const fn not(n: u256) -> u256 {
    u256::new(!n.low(), !n.high())
}

/// Const implementation of `Eq` for internal algorithm use.
#[inline(always)]
const fn eq(lhs: u256, rhs: u256) -> bool {
    lhs.low() == rhs.low() && lhs.high() == rhs.high()
}

/// Const implementation of `PartialOrd::lt` for internal algorithm use.
#[inline(always)]
pub(crate) const fn lt(lhs: u256, rhs: u256) -> bool {
    lhs.high() < rhs.high() || (lhs.high() == rhs.high() && lhs.low() < rhs.low())
}

/// Const implementation of `PartialOrd::le` for internal algorithm use.
#[inline(always)]
const fn le(lhs: u256, rhs: u256) -> bool {
    lhs.high() < rhs.high() || (lhs.high() == rhs.high() && lhs.low() <= rhs.low())
}

/// Const implementation of `PartialOrd::gt` for internal algorithm use.
#[inline(always)]
const fn gt(lhs: u256, rhs: u256) -> bool {
    lhs.high() > rhs.high() || (lhs.high() == rhs.high() && lhs.low() > rhs.low())
}

/// Const implementation of `PartialOrd::ge` for internal algorithm use.
#[inline(always)]
const fn ge(lhs: u256, rhs: u256) -> bool {
    lhs.high() > rhs.high() || (lhs.high() == rhs.high() && lhs.low() >= rhs.low())
}

/// Const implementation of `PartialOrd::cmp` for internal algorithm use.
#[inline(always)]
const fn cmp(lhs: u256, rhs: u256) -> Ordering {
    if lhs.high() < rhs.high() {
        Ordering::Less
    } else if lhs.high() > rhs.high() {
        Ordering::Greater
    } else if lhs.low() < rhs.low() {
        Ordering::Less
    } else if lhs.low() > rhs.low() {
        Ordering::Greater
    } else {
        Ordering::Equal
    }
}

#[inline]
fn to_bytes(mut value: u256, buffer: &mut [u8; 78]) -> &[u8] {
    // We're not optimizing for this at all, since we'll implement
    // it well in the integer writers (max 78 digits).

    // only want to write until
    let mut rem: u64;
    let mut index = buffer.len();
    while value.high() > 0 || value.low() > 10 && index > 1 {
        index -= 1;
        (value, rem) = value.div_rem_ulimb(10);
        buffer[index] = b'0' + rem as u8;
    }
    // always have one trailing digit
    index -= 1;
    buffer[index] = b'0' + value.low() as u8;
    &buffer[index..]
}

#[inline]
fn to_string(value: u256, buffer: &mut [u8; 78]) -> Result<&str, Utf8Error> {
    str::from_utf8(to_bytes(value, buffer))
}

from_str_radix_impl!(u256, false);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_test() {
        // NOTE: This is mostly covered elsewhere
        assert_eq!(u256::from_u8(1).wrapping_add(u256::from_u8(1)), u256::from_u8(2));
        assert_eq!(u256::MAX.wrapping_add(u256::MAX), u256::new(u128::MAX - 1, u128::MAX));

        assert_eq!(
            u256::from_u8(1).overflowing_add(u256::from_u8(1)).0,
            u256::from_u8(1).wrapping_add(u256::from_u8(1))
        );
        assert_eq!(u256::MAX.overflowing_add(u256::MAX).0, u256::MAX.wrapping_add(u256::MAX));
    }

    #[test]
    fn display_test() {
        let max = u256::MAX;
        let result = max.to_string();
        assert_eq!(
            "115792089237316195423570985008687907853269984665640564039457584007913129639935",
            result
        );

        let value = u256::new(0, 1);
        let result = value.to_string();
        assert_eq!("340282366920938463463374607431768211456", result);
    }

    #[test]
    fn lower_exp_test() {
        let max = u256::MAX;
        let result = format!("{:e}", max);
        assert_eq!(
            "1.15792089237316195423570985008687907853269984665640564039457584007913129639935e77",
            result
        );

        let value = u256::new(0, 1);
        let result = format!("{:e}", value);
        assert_eq!("3.40282366920938463463374607431768211456e38", result);
    }

    #[test]
    fn upper_exp_test() {
        let max = u256::MAX;
        let result = format!("{:E}", max);
        assert_eq!(
            "1.15792089237316195423570985008687907853269984665640564039457584007913129639935E77",
            result
        );

        let value = u256::new(0, 1);
        let result = format!("{:E}", value);
        assert_eq!("3.40282366920938463463374607431768211456E38", result);
    }

    #[inline(always)]
    fn parse(expected: u256, radix: u32, s: &str) {
        // check a full roundtrip
        let res: Result<u256, ParseIntError> = u256::from_str_radix(s, radix);
        assert!(res.is_ok());
        let actual = res.unwrap();
        assert_eq!(expected, actual);

        let as_str = actual.to_string();
        let res: Result<u256, ParseIntError> = u256::from_str_radix(&as_str, 10);
        assert!(res.is_ok());
        let actual = res.unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn from_str_radix_test() {
        let cases = [
            (
                u256::MAX,
                10,
                "115792089237316195423570985008687907853269984665640564039457584007913129639935",
            ),
            (
                u256::MAX,
                10,
                "+115792089237316195423570985008687907853269984665640564039457584007913129639935",
            ),
            (u256::MAX, 16, "+ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"),
            (0xffffffffffffffffu128.into(), 16, "+ffffffffffffffff"),
            (0x123456789ab123u128.into(), 10, "5124095576027427"),
            (0x123456789ab123u128.into(), 16, "+123456789ab123"),
        ];
        for case in cases {
            parse(case.0, case.1, case.2);
        }

        let failing = [
            (10, "-15"),
            (16, "-0xFF"),
            (16, "+0xFF"),
            (16, "0xFF"),
            (10, "FF"),
            (10, "a9"),
            (10, "12.34"),
            (10, "1234_67"),
            (10, "115792089237316195423570985008687907853269984665640564039457584007913129639936"),
        ];
        for case in failing {
            let res: Result<u256, ParseIntError> = u256::from_str_radix(case.1, case.0);
            assert!(res.is_err());
        }
    }

    #[test]
    #[should_panic]
    fn from_str_radix_neg_test() {
        _ = u256::from_str_radix("-123", 10).unwrap();
    }
}
