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
        let (lo, hi) = math::shr_i128(self.low(), self.high(), rhs % Self::BITS);
        Self::new(lo, hi)
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
