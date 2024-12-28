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

use super::shared_macros::*;
use crate::{math, u256, ILimb, TryFromIntError, ULimb};

int_define!(
    name => i256,
    bits => 256,
    kind => signed,
);

impl i256 {
    int_impl_define!(
        self => i256,
        unsigned_t => u256,
        unsigned_wide_t => u128,
        signed_wide_t => i128,
        bits => 256,
        max_digits => 77,
        kind => signed,
        short_circuit => false,
    );

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

    /// Create the 256-bit signed integer from an `i256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn from_signed(value: i256) -> Self {
        Self::from_i256(value)
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

    /// Convert the 256-bit signed integer to an `u256`, as if by an `as` cast.
    #[inline(always)]
    pub const fn as_signed(&self) -> Self {
        self.as_i256()
    }
}

int_traits_define!(type => i256, unsigned_type => u256);

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
