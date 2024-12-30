//! Casts between primitive and signed <-> unsigned big integers.

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

/// And any `as_` and `from_` methods for higher-order types.
macro_rules! define {
    (
        unsigned_type => $u_t:ty,
        signed_type => $s_t:ty,
        bits => $bits:expr,
        kind => $kind:ident $(,)?
    ) => {
        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a `u8`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_u8(value: u8) -> Self {
            Self::from_u32(value as u32)
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a `u16`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_u16(value: u16) -> Self {
            Self::from_u32(value as u32)
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a `u32`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_u32(value: u32) -> Self {
            let mut limbs = [0; Self::LIMBS];
            ne_index!(limbs[0] = value as $crate::ULimb);
            Self::from_ne_limbs(limbs)
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a `u64`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_u64(value: u64) -> Self {
            const BITS: u32 = $crate::ULimb::BITS;
            assert!(BITS == 32 || BITS == 64);

            let mut limbs = [0; Self::LIMBS];
            if BITS == 32 {
                ne_index!(limbs[0] = value as $crate::ULimb);
                ne_index!(limbs[1] = (value >> 32) as $crate::ULimb);
            } else {
                ne_index!(limbs[0] = value as $crate::ULimb);
            }
            Self::from_ne_limbs(limbs)
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a `u128`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_u128(value: u128) -> Self {
            const BITS: u32 = $crate::ULimb::BITS;
            assert!(BITS == 32 || BITS == 64);

            let mut limbs = [0; Self::LIMBS];
            if BITS == 32 {
                ne_index!(limbs[0] = value as $crate::ULimb);
                ne_index!(limbs[1] = (value >> 32) as $crate::ULimb);
                ne_index!(limbs[2] = (value >> 64) as $crate::ULimb);
                ne_index!(limbs[3] = (value >> 96) as $crate::ULimb);
            } else {
                ne_index!(limbs[0] = value as $crate::ULimb);
                ne_index!(limbs[1] = (value >> 64) as $crate::ULimb);
            }
            Self::from_ne_limbs(limbs)
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an unsigned limb, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn from_ulimb(value: $crate::ULimb) -> Self {
            const BITS: u32 = $crate::ULimb::BITS;
            assert!(BITS == 32 || BITS == 64);
            if BITS == 32 {
                Self::from_u32(value as u32)
            } else {
                Self::from_u64(value as u64)
            }
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an unsigned wide type, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn from_uwide(value: $crate::UWide) -> Self {
            const BITS: u32 = $crate::UWide::BITS;
            assert!(BITS == 64 || BITS == 128);
            if BITS == 64 {
                Self::from_u64(value as u64)
            } else {
                Self::from_u128(value as u128)
            }
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an unsigned integer, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_unsigned(value: $u_t) -> Self {
            Self::from_ne_limbs(value.to_ne_limbs())
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a signed integer, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_signed(value: $s_t) -> Self {
            Self::from_ne_limbs(value.to_ne_limbs())
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an `i8`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_i8(value: i8) -> Self {
            Self::from_i32(value as i32)
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an `i16`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_i16(value: i16) -> Self {
            Self::from_i32(value as i32)
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an `i32`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_i32(value: i32) -> Self {
            const BITS: u32 = $crate::ULimb::BITS;
            assert!(BITS == 32 || BITS == 64);
            if BITS == 32 {
                let sign_bit = $crate::ULimb::MIN.wrapping_sub(value.is_negative() as $crate::ULimb);
                let mut limbs = [sign_bit; Self::LIMBS];
                let value = value as $crate::ULimb;
                ne_index!(limbs[0] = value);
                Self::from_ne_limbs(limbs)
            } else {
                Self::from_i64(value as i64)
            }
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an `i64`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_i64(value: i64) -> Self {
            const BITS: u32 = $crate::ULimb::BITS;
            assert!(BITS == 32 || BITS == 64);
            if BITS == 32 {
                Self::from_i32(value as i32)
            } else {
                let sign_bit = $crate::ULimb::MIN.wrapping_sub(value.is_negative() as $crate::ULimb);
                let mut limbs = [sign_bit; Self::LIMBS];
                let value = value as $crate::ULimb;
                ne_index!(limbs[0] = value);
                Self::from_ne_limbs(limbs)
            }
        }

        /// Create the 256-bit unsigned integer from an `i128`, as if by an `as`
        /// cast.
        #[inline(always)]
        pub const fn from_i128(value: i128) -> Self {
            const BITS: u32 = $crate::ULimb::BITS;
            assert!(BITS == 32 || BITS == 64);

            let sign_bit = $crate::ULimb::MIN.wrapping_sub(value.is_negative() as $crate::ULimb);
            let mut limbs = [sign_bit; Self::LIMBS];
            let value = value as u128;
            if BITS == 32 {
                ne_index!(limbs[0] = value as $crate::ULimb);
                ne_index!(limbs[1] = (value >> 32) as $crate::ULimb);
                ne_index!(limbs[2] = (value >> 64) as $crate::ULimb);
                ne_index!(limbs[3] = (value >> 96) as $crate::ULimb);
            } else {
                ne_index!(limbs[0] = value as $crate::ULimb);
                ne_index!(limbs[1] = (value >> 64) as $crate::ULimb);
            }
            Self::from_ne_limbs(limbs)
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a signed limb, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn from_ilimb(value: $crate::ILimb) -> Self {
            const BITS: u32 = $crate::ULimb::BITS;
            assert!(BITS == 32 || BITS == 64);
            if BITS == 32 {
                Self::from_i32(value as i32)
            } else {
                Self::from_i64(value as i64)
            }
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a wide type, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn from_iwide(value: $crate::IWide) -> Self {
            const BITS: u32 = $crate::UWide::BITS;
            assert!(BITS == 64 || BITS == 128);
            if BITS == 64 {
                Self::from_i64(value as i64)
            } else {
                Self::from_i128(value as i128)
            }
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to a `u8`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_u8(&self) -> u8 {
            self.as_u32() as u8
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to a `u16`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_u16(&self) -> u16 {
            self.as_u32() as u16
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to a `u32`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_u32(&self) -> u32 {
            const BITS: u32 = $crate::ULimb::BITS;
            assert!(BITS == 32 || BITS == 64);
            let limbs = self.to_ne_limbs();
            ne_index!(limbs[0]) as u32
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to a `u64`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_u64(&self) -> u64 {
            const BITS: u32 = $crate::ULimb::BITS;
            assert!(BITS == 32 || BITS == 64);

            let limbs = self.to_ne_limbs();
            if BITS == 32 {
                let x0 = ne_index!(limbs[0]) as u64;
                let x1 = ne_index!(limbs[1]) as u64;
                (x0 | (x1 << 32))
            } else {
                ne_index!(limbs[0]) as u64
            }
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " an unsigned limb, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn as_ulimb(&self) -> $crate::ULimb {
            const BITS: u32 = $crate::ULimb::BITS;
            assert!(BITS == 32 || BITS == 64);
            if BITS == 32 {
                self.as_u32() as $crate::ULimb
            } else {
                self.as_u64() as $crate::ULimb
            }
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to a `u128`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_u128(&self) -> u128 {
            const BITS: u32 = $crate::ULimb::BITS;
            assert!(BITS == 32 || BITS == 64);

            let limbs = self.to_ne_limbs();
            if BITS == 32 {
                let x0 = ne_index!(limbs[0]) as u128;
                let x1 = ne_index!(limbs[1]) as u128;
                let x2 = ne_index!(limbs[2]) as u128;
                let x3 = ne_index!(limbs[3]) as u128;
                (x0 | (x1 << 32) | (x2 << 64)| (x3 << 96))
            } else {
                let x0 = ne_index!(limbs[0]) as u128;
                let x1 = ne_index!(limbs[1]) as u128;
                (x0 | (x1 << 64))
            }
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " an unsigned wide type, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn as_uwide(&self) -> $crate::UWide {
            const BITS: u32 = $crate::UWide::BITS;
            assert!(BITS == 64 || BITS == 128);
            if BITS == 64 {
                self.as_u64() as $crate::UWide
            } else {
                self.as_u128() as $crate::UWide
            }
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to an `i8`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_i8(&self) -> i8 {
            self.as_u8() as i8
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to an `i16`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_i16(&self) -> i16 {
            self.as_u16() as i16
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to an `i32`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_i32(&self) -> i32 {
            self.as_u32() as i32
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to an `i64`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_i64(&self) -> i64 {
            self.as_u64() as i64
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to a `i128`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_i128(&self) -> i128 {
            self.as_u128() as i128
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " a signed limb, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn as_ilimb(&self) -> $crate::ILimb {
            self.as_ulimb() as $crate::ILimb
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " a signed wide type, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn as_iwide(&self) -> $crate::IWide {
            self.as_uwide() as $crate::IWide
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " unsigned integer to the unsigned type, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_unsigned(&self) -> $u_t {
            <$u_t>::from_ne_limbs(self.to_ne_limbs())
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " unsigned integer to the signed type, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_signed(&self) -> $s_t {
            <$s_t>::from_ne_limbs(self.to_ne_limbs())
        }
    };
}

pub(crate) use define;
