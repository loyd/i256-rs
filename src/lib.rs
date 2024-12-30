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
#![allow(non_camel_case_types)]

// FIXME: Older versions of nightly may require the features
// `const_bigint_helper_methods`. Remove this comment on 2025/01/01.

// NOTE: All this has to be defined via macros, due to the lack of full
// const generic support with associated constants, so we need to define
// the traits with macros at the high level, for transmutes, etc.

#[macro_use]
mod util;

mod error;
mod int;
mod parse;
mod shared;
mod types;
mod uint;
mod write;

// exposed only for testing
pub mod math;

pub use error::{IntErrorKind, ParseIntError, TryFromIntError};
pub use types::{ILimb, IWide, ULimb, UWide};

/// Define a new signed and unsigned integer pair
///
/// Sample use is:
///
/// ```rust,ignore
/// crate::define!(
///     unsigned => u256,
///     signed => i256,
///     unsigned_wide => u128,
///     signed_wide => i128,
///     bits => 256,
/// );
/// ```
///
/// Both types must have a signed and unsigned variant.
macro_rules! define {
    (
        unsigned => $unsigned:ident,
        signed => $signed:ident,
        unsigned_wide => $unsigned_wide:ty,
        signed_wide => $signed_wide:ty,
        bits => $bits:literal,
    ) => {
        crate::int::define!(
            name => $signed,
            unsigned_t => $unsigned,
            unsigned_wide_t => $unsigned_wide,
            signed_wide_t => $signed_wide,
            bits => $bits,
        );
        crate::uint::define!(
            name => $unsigned,
            signed_t => $signed,
            signed_wide_t => $signed_wide,
            unsigned_wide_t => $unsigned_wide,
            bits => $bits,
        );
    };
}

define!(
    unsigned => U256,
    signed => I256,
    unsigned_wide => u128,
    signed_wide => i128,
    bits => 256,
);

pub type u256 = U256;
pub type i256 = I256;

#[cfg(test)]
mod u256_tests {
    use super::*;

    #[test]
    fn add_test() {
        // NOTE: This is mostly covered elsewhere
        assert_eq!(u256::from_u8(1).wrapping_add(u256::from_u8(1)), u256::from_u8(2));
        assert_eq!(
            u256::MAX.wrapping_add(u256::MAX),
            u256::from_le_u64([u64::MAX - 1, u64::MAX, u64::MAX, u64::MAX])
        );

        assert_eq!(
            u256::from_u8(1).overflowing_add(u256::from_u8(1)).0,
            u256::from_u8(1).wrapping_add(u256::from_u8(1))
        );
        assert_eq!(u256::MAX.overflowing_add(u256::MAX).0, u256::MAX.wrapping_add(u256::MAX));
    }

    #[test]
    fn endian_tests() {
        let data = [0x123456u64, 0x789abcu64, 0xdef012u64, 0x345678u64];
        let int = u256::from_le_u64(data);
        assert_eq!(int, u256::from_le_bytes(int.to_le_bytes()));
        assert_eq!(int, u256::from_be_bytes(int.to_be_bytes()));
        assert_eq!(int, u256::from_ne_bytes(int.to_ne_bytes()));

        assert_eq!(int, u256::from_le_limbs(int.to_le_limbs()));
        assert_eq!(int, u256::from_be_limbs(int.to_be_limbs()));
        assert_eq!(int, u256::from_ne_limbs(int.to_ne_limbs()));

        assert_eq!(int, u256::from_le_wide(int.to_le_wide()));
        assert_eq!(int, u256::from_be_wide(int.to_be_wide()));
        assert_eq!(int, u256::from_ne_wide(int.to_ne_wide()));

        assert_eq!(int, u256::from_le_u32(int.to_le_u32()));
        assert_eq!(int, u256::from_be_u32(int.to_be_u32()));
        assert_eq!(int, u256::from_ne_u32(int.to_ne_u32()));

        assert_eq!(int, u256::from_le_u64(int.to_le_u64()));
        assert_eq!(int, u256::from_be_u64(int.to_be_u64()));
        assert_eq!(int, u256::from_ne_u64(int.to_ne_u64()));
    }

    #[test]
    fn display_test() {
        let max = u256::MAX;
        let result = max.to_string();
        assert_eq!(
            "115792089237316195423570985008687907853269984665640564039457584007913129639935",
            result
        );

        let value = u256::from_le_u64([0, 0, 1, 0]);
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

        let value = u256::from_le_u64([0, 0, 1, 0]);
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

        let value = u256::from_le_u64([0, 0, 1, 0]);
        let result = format!("{:E}", value);
        assert_eq!("3.40282366920938463463374607431768211456E38", result);
    }

    #[test]
    fn octal_test() {
        let max = u256::MAX;
        let result = format!("{:o}", max);
        assert_eq!(
            "17777777777777777777777777777777777777777777777777777777777777777777777777777777777777",
            result
        );

        let result = format!("{:#o}", max);
        assert_eq!(
            "0o17777777777777777777777777777777777777777777777777777777777777777777777777777777777777",
            result
        );

        let value = u256::from_le_u64([0, 0, 1, 0]);
        let result = format!("{:o}", value);
        assert_eq!("4000000000000000000000000000000000000000000", result);
    }

    #[test]
    fn binary_test() {
        let max = u256::MAX;
        let result = format!("{:b}", max);
        assert_eq!(
            "1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111",
            result
        );

        let result = format!("{:#b}", max);
        assert_eq!(
            "0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111",
            result
        );

        let value = u256::from_le_u64([0, 0, 1, 0]);
        let result = format!("{:b}", value);
        assert_eq!(
            "100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
            result
        );
    }

    #[test]
    fn lower_hex_test() {
        let max = u256::MAX;
        let result = format!("{:x}", max);
        assert_eq!("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", result);

        let result = format!("{:#x}", max);
        assert_eq!("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", result);

        let value = u256::from_le_u64([0, 0, 1, 0]);
        let result = format!("{:x}", value);
        assert_eq!("100000000000000000000000000000000", result);
    }

    #[test]
    fn upper_hex_test() {
        let max = u256::MAX;
        let result = format!("{:X}", max);
        assert_eq!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", result);

        let result = format!("{:#X}", max);
        assert_eq!("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", result);

        let value = u256::from_le_u64([0, 0, 1, 0]);
        let result = format!("{:X}", value);
        assert_eq!("100000000000000000000000000000000", result);
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

#[cfg(test)]
mod i256_tests {
    use super::*;

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
