//! Macros shared between signed and unsigned types.

// FIXME: Add support for [Saturating][core::num::Saturating] and
// [Wrapping][core::num::Wrapping] when we drop support for <1.74.0.

macro_rules! int_define {
    ($name:ident, $bits:literal, $kind:ident) => {
        #[doc = concat!("The ", stringify!($bits), "-bit ", stringify!($kind), " integer type.")]
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
        /// Note that this type is **NOT** safe to use in FFIs, since the
        /// underlying storage may use [`128-bit`] integers in the future
        /// which are not FFI-safe. If you would like to use this type
        /// within a FFI, use [`to_le_bytes`] and [`to_be_bytes`].
        #[doc = concat!("[`to_le_bytes`]: ", stringify!($name), "::to_le_bytes")]
        #[doc = concat!("[`to_be_bytes`]: ", stringify!($name), "::to_be_bytes")]
        #[doc = concat!("[`high`]: ", stringify!($name), "::high")]
        #[doc = concat!("[`low`]: ", stringify!($name), "::low")]
        /// [`alternate`]: fmt::Formatter::alternate
        /// [`Binary`]: fmt::Binary
        /// [`128-bit`]: https://rust-lang.github.io/unsafe-code-guidelines/layout/scalars.html#fixed-width-integer-types
        #[allow(non_camel_case_types)]
        #[derive(Copy, Clone, Default, PartialEq, Eq, Hash)]
        pub struct $name {
            // NOTE: This is currently FFI-safe (if we did repr(C)) but we
            // intentionally make  no guarantees so we're free to re-arrange
            // the layout.
            limbs: [$crate::ULimb; $bits / core::mem::size_of::<$crate::ULimb>() / 8],
        }
    };
}

/// Define the high and low implementations for 4 limb implementations.
///
/// This is specific for **ONLY** our 256-bit integers (4x 64-bit limbs).
macro_rules! high_low_define {
    ($t:ty, $lo_t:ty, $hi_t:ty, $kind:ident) => {
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
        const fn to_flat_bytes(x: [u8; 16], y: [u8; 16]) -> [u8; Self::BYTES] {
            // SAFETY: plain old data
            unsafe { core::mem::transmute::<[[u8; 16]; 2], [u8; Self::BYTES]>([x, y]) }
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
        const fn from_flat_bytes(bytes: [u8; Self::BYTES]) -> ([u8; 16], [u8; 16]) {
            // SAFETY: plain old data
            let r = unsafe { core::mem::transmute::<[u8; Self::BYTES], [[u8; 16]; 2]>(bytes) };
            (r[0], r[1])
        }

        #[doc = concat!("Create a new `", stringify!($t), "` from the low and high bits.")]
        #[inline(always)]
        pub const fn new(lo: $lo_t, hi: $hi_t) -> Self {
            let inst = if cfg!(target_endian = "big") {
                Self::from_be_bytes(Self::to_flat_bytes(hi.to_be_bytes(), lo.to_be_bytes()))
            } else {
                Self::from_le_bytes(Self::to_flat_bytes(lo.to_le_bytes(), hi.to_le_bytes()))
            };
            assert!(inst.limbs.len() ==  4, "cannot create type with more than 4 limbs.");

            inst
        }

        #[doc = concat!("/// Get the high ", stringify!($crate::ULimb::BITS), " bits of the ", stringify!($kind), " integer.")]
        #[inline(always)]
        pub const fn high(self) -> $hi_t {
            assert!(self.limbs.len() ==  4, "cannot get high bits with more than 4 limbs.");
            if cfg!(target_endian = "big") {
                let (hi, _) = Self::from_flat_bytes(self.to_be_bytes());
                <$hi_t>::from_be_bytes(hi)
            } else {
                let (_, hi) = Self::from_flat_bytes(self.to_le_bytes());
                <$hi_t>::from_le_bytes(hi)
            }
        }

        #[doc = concat!("/// Get the low ", stringify!($crate::ULimb::BITS), " bits of the ", stringify!($kind), " integer.")]
        #[inline(always)]
        pub const fn low(self) -> $lo_t {
            assert!(self.limbs.len() ==  4, "cannot get low bits with more than 4 limbs.");
            if cfg!(target_endian = "big") {
                let (_, lo) = Self::from_flat_bytes(self.to_be_bytes());
                <$lo_t>::from_be_bytes(lo)
            } else {
                let (lo, _) = Self::from_flat_bytes(self.to_le_bytes());
                <$lo_t>::from_le_bytes(lo)
            }
        }

        /// Const implementation of `BitAnd`.
        #[inline(always)]
        pub const fn bitand_const(self, rhs: Self) -> Self {
            Self::new(self.low() & rhs.low(), self.high() & rhs.high())
        }

        /// Const implementation of `BitOr`.
        #[inline(always)]
        pub const fn bitor_const(self, rhs: Self) -> Self {
            Self::new(self.low() | rhs.low(), self.high() | rhs.high())
        }

        /// Const implementation of `BitXor`.
        #[inline(always)]
        pub const fn bitxor_const(self, rhs: Self) -> Self {
            Self::new(self.low() ^ rhs.low(), self.high() ^ rhs.high())
        }

        /// Const implementation of `Not`.
        #[inline(always)]
        pub const fn not_const(self) -> Self {
            Self::new(!self.low(), !self.high())
        }

        /// Const implementation of `Eq`.
        #[inline(always)]
        pub const fn eq_const(self, rhs: Self) -> bool {
            self.low() == rhs.low() && self.high() == rhs.high()
        }

        // NOTE: Because of two's complement, these comparisons are always normal.
        /// Const implementation of `PartialOrd::lt`.
        #[inline(always)]
        pub const fn lt_const(self, rhs: Self) -> bool {
            self.high() < rhs.high() || (self.high() == rhs.high() && self.low() < rhs.low())
        }

        /// Const implementation of `PartialOrd::le`.
        #[inline(always)]
        pub const fn le_const(self, rhs: Self) -> bool {
            self.high() < rhs.high() || (self.high() == rhs.high() && self.low() <= rhs.low())
        }

        /// Const implementation of `PartialOrd::gt`.
        #[inline(always)]
        pub const fn gt_const(self, rhs: Self) -> bool {
            self.high() > rhs.high() || (self.high() == rhs.high() && self.low() > rhs.low())
        }

        /// Const implementation of `PartialOrd::ge`.
        #[inline(always)]
        pub const fn ge_const(self, rhs: Self) -> bool {
            self.high() > rhs.high() || (self.high() == rhs.high() && self.low() >= rhs.low())
        }

        /// Const implementation of `PartialOrd::cmp`.
        #[inline(always)]
        pub const fn cmp_const(self, rhs: Self) -> core::cmp::Ordering {
            let x0 = self.low();
            let x1 = self.high();
            let y0 = rhs.low();
            let y1 = rhs.high();
            if x1 < y1 {
                core::cmp::Ordering::Less
            } else if x1 > y1 {
                core::cmp::Ordering::Greater
            } else if x0 < y0 {
                core::cmp::Ordering::Less
            } else if x0 > y0 {
                core::cmp::Ordering::Greater
            } else {
                core::cmp::Ordering::Equal
            }
        }
    };
}

/// In order for this to be correctly implemented, the following
/// helpers must be defined:
/// - `Self::from_u128`
/// - `Self::from_i128`
/// - `Self::from_u256`
/// - `Self::from_i256`
/// - `Self::as_u128`
/// - `Self::as_i128`
/// - `Self::as_u256`
/// - `Self::as_i256`
///
/// And any `as_` and `from_` methods for higher-order types.
macro_rules! extensions_define {
    ($bits:expr, $kind:ident) => {
        /// Get the limb indexing from the least-significant order.
        #[inline(always)]
        const fn limb(self, index: usize) -> $crate::ULimb {
            if cfg!(target_endian = "big") {
                self.limbs[self.limbs.len() - 1 - index]
            } else {
                self.limbs[index]
            }
        }

        /// Get if the integer is even.
        #[inline(always)]
        pub const fn is_even(self) -> bool {
            self.limb(0) % 2 == 0
        }

        /// Get if the integer is odd.
        #[inline(always)]
        pub const fn is_odd(self) -> bool {
            !self.is_even()
        }

        #[doc = concat!("/// Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a `u8`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_u8(value: u8) -> Self {
            Self::from_u128(value as u128)
        }

        #[doc = concat!("/// Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a `u16`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_u16(value: u16) -> Self {
            Self::from_u128(value as u128)
        }

        #[doc = concat!("/// Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a `u32`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_u32(value: u32) -> Self {
            Self::from_u128(value as u128)
        }

        #[doc = concat!("/// Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a `u64`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_u64(value: u64) -> Self {
            Self::from_u128(value as u128)
        }

        #[doc = concat!("/// Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an unsigned limb, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn from_ulimb(value: $crate::ULimb) -> Self {
            Self::from_u128(value as u128)
        }

        #[doc = concat!("/// Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an unsigned wide type, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn from_uwide(value: $crate::UWide) -> Self {
            Self::from_u128(value as u128)
        }

        #[doc = concat!("/// Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an `i8`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_i8(value: i8) -> Self {
            Self::from_i128(value as i128)
        }

        #[doc = concat!("/// Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an `i16`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_i16(value: i16) -> Self {
            Self::from_i128(value as i128)
        }

        #[doc = concat!("/// Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an `i32`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_i32(value: i32) -> Self {
            Self::from_i128(value as i128)
        }

        #[doc = concat!("/// Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an `i64`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_i64(value: i64) -> Self {
            Self::from_i128(value as i128)
        }

        #[doc = concat!("/// Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a signed limb, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn from_ilimb(value: $crate::ILimb) -> Self {
            Self::from_i128(value as i128)
        }

        #[doc = concat!("/// Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a signed wide type, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn from_iwide(value: $crate::IWide) -> Self {
            Self::from_i128(value as i128)
        }

        #[doc = concat!("/// Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to a `u8`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_u8(&self) -> u8 {
            self.as_u32() as u8
        }

        #[doc = concat!("/// Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to a `u16`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_u16(&self) -> u16 {
            self.as_u32() as u16
        }

        #[doc = concat!("/// Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to a `u32`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_u32(&self) -> u32 {
            self.as_u128() as u32
        }

        #[doc = concat!("/// Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to a `u64`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_u64(&self) -> u64 {
            self.as_u128() as u64
        }

        #[doc = concat!("/// Convert the ", stringify!($bits), "-bit ", stringify!($kind), " an unsigned limb, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn as_ulimb(&self) -> $crate::ULimb {
            assert!($crate::ULimb::BITS <= 128);
            self.as_u128() as $crate::ULimb
        }

        #[doc = concat!("/// Convert the ", stringify!($bits), "-bit ", stringify!($kind), " an unsigned wide type, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn as_uwide(&self) -> $crate::UWide {
            assert!($crate::UWide::BITS <= 128);
            self.as_u128() as $crate::UWide
        }

        #[doc = concat!("/// Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to an `i8`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_i8(&self) -> i8 {
            self.as_i128() as i8
        }

        #[doc = concat!("/// Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to an `i16`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_i16(&self) -> i16 {
            self.as_i128() as i16
        }

        #[doc = concat!("/// Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to an `i32`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_i32(&self) -> i32 {
            self.as_i128() as i32
        }

        #[doc = concat!("/// Convert the ", stringify!($bits), "-bit ", stringify!($kind), " to an `i64`, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_i64(&self) -> i64 {
            self.as_i128() as i64
        }

        #[doc = concat!("/// Convert the ", stringify!($bits), "-bit ", stringify!($kind), " a signed limb, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn as_ilimb(&self) -> $crate::ILimb {
            assert!($crate::ILimb::BITS <= 128);
            self.as_i128() as $crate::ILimb
        }

        #[doc = concat!("/// Convert the ", stringify!($bits), "-bit ", stringify!($kind), " a signed wide type, as if by an `as` cast.")]
        #[inline(always)]
        #[allow(clippy::unnecessary_cast)]
        pub const fn as_iwide(&self) -> $crate::IWide {
            assert!($crate::IWide::BITS <= 128);
            self.as_i128() as $crate::IWide
        }
    };
}

/// Define the byte swap accessory methods.
///
/// In order for this to be correctly implemented, the following
/// helpers must be defined:
/// - `Self::swap_bytes`
macro_rules! convert_define {
    ($t:ty, $wide_t:ty) => {
        /// The number of bytes in the type.
        const BYTES: usize = Self::BITS as usize / 8;

        /// The number of limbs in the type.
        const LIMBS: usize = Self::BYTES / core::mem::size_of::<$crate::ULimb>();

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
        const fn from_limbs(limbs: [ULimb; Self::LIMBS]) -> [u8; Self::BYTES] {
            // SAFETY: This is plain old data
            unsafe { core::mem::transmute::<[ULimb; Self::LIMBS], [u8; Self::BYTES]>(limbs) }
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
        const fn to_limbs(bytes: [u8; Self::BYTES]) -> [ULimb; Self::LIMBS] {
            // SAFETY: This is plain old data
            unsafe { core::mem::transmute(bytes) }
        }

        /// Returns the memory representation of this integer as a byte array in
        /// big-endian (network) byte order.
        ///
        /// See [`i128::to_be_bytes`].
        #[inline(always)]
        pub const fn to_be_bytes(self) -> [u8; Self::BYTES] {
            Self::from_limbs(self.to_be_limbs())
        }

        /// Returns the memory representation of this integer as a byte array in
        /// little-endian byte order.
        ///
        /// See [`i128::to_le_bytes`].
        #[inline(always)]
        pub const fn to_le_bytes(self) -> [u8; Self::BYTES] {
            Self::from_limbs(self.to_le_limbs())
        }

        /// Returns the memory representation of this as a series of limbs in
        /// big-endian (network) byte order.
        #[inline(always)]
        pub const fn to_be_limbs(self) -> [ULimb; Self::LIMBS] {
            self.to_be().limbs
        }

        /// Returns the memory representation of this as a series of limbs in
        /// little-endian byte order.
        #[inline(always)]
        pub const fn to_le_limbs(self) -> [ULimb; Self::LIMBS] {
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
        pub const fn to_ne_limbs(self) -> [ULimb; Self::LIMBS] {
            self.limbs
        }

        /// Returns the memory representation of this integer as a byte array in
        /// native byte order.
        ///
        /// As the target platform's native endianness is used, portable code
        /// should use [`to_be_bytes`] or [`to_le_bytes`], as appropriate,
        /// instead.
        ///
        /// See [`i128::to_ne_bytes`].
        ///
        /// [`to_be_bytes`]: Self::to_be_bytes
        /// [`to_le_bytes`]: Self::to_le_bytes
        #[inline(always)]
        pub const fn to_ne_bytes(self) -> [u8; Self::BYTES] {
            Self::from_limbs(self.to_ne_limbs())
        }

        /// Creates a native endian integer value from its representation
        /// as a byte array in big endian.
        ///
        /// See [`i128::from_be_bytes`].
        #[inline(always)]
        pub const fn from_be_bytes(bytes: [u8; Self::BYTES]) -> Self {
            Self::from_be_limbs(Self::to_limbs(bytes))
        }

        /// Creates a native endian integer value from its representation
        /// as a byte array in little endian.
        ///
        /// See [`i128::from_le_bytes`].
        #[inline(always)]
        pub const fn from_le_bytes(bytes: [u8; Self::BYTES]) -> Self {
            Self::from_le_limbs(Self::to_limbs(bytes))
        }

        /// Creates a native endian integer value from its memory representation
        /// as a byte array in native endianness.
        ///
        /// As the target platform's native endianness is used, portable code
        /// likely wants to use [`from_be_bytes`] or [`from_le_bytes`], as
        /// appropriate instead.
        ///
        /// See [`i128::from_ne_bytes`].
        ///
        /// [`from_be_bytes`]: Self::from_be_bytes
        /// [`from_le_bytes`]: Self::from_le_bytes
        #[inline(always)]
        pub const fn from_ne_bytes(bytes: [u8; Self::BYTES]) -> Self {
            Self::from_ne_limbs(Self::to_limbs(bytes))
        }

        /// Swap the order of limbs, useful for re-arranging for BE/LE order.
        #[inline(always)]
        const fn swap_limbs(limbs: [ULimb; Self::LIMBS]) -> [ULimb; Self::LIMBS] {
            let mut res = [0; Self::LIMBS];
            let mut i = 0;
            while i < Self::LIMBS {
                res[i] = limbs[Self::LIMBS - i - 1];
                i += 1;
            }
            res
        }

        /// Creates a native endian integer value from its representation
        /// as limbs in big endian.
        #[inline(always)]
        pub const fn from_be_limbs(limbs: [ULimb; Self::LIMBS]) -> Self {
            if cfg!(target_endian = "big") {
                Self::from_ne_limbs(limbs)
            } else {
                Self::from_ne_limbs(Self::swap_limbs(limbs))
            }
        }

        /// Creates a native endian integer value from its representation
        /// as limbs in little endian.
        #[inline(always)]
        pub const fn from_le_limbs(limbs: [ULimb; Self::LIMBS]) -> Self {
            if cfg!(target_endian = "big") {
                Self::from_ne_limbs(Self::swap_limbs(limbs))
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
        pub const fn from_ne_limbs(limbs: [ULimb; Self::LIMBS]) -> Self {
            Self {
                limbs,
            }
        }
    };
}

/// Defines some of the bitwise operator definitions.
///
/// See the bench on `bit_algos` for some of the choices.
macro_rules! bitops_define {
    ($wide_t:ty) => {
        /// Returns the number of ones in the binary representation of `self`.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::count_ones`].")]
        #[inline(always)]
        pub const fn count_ones(self) -> u32 {
            // NOTE: Rust vectorizes this nicely on x86_64.
            let mut count = 0;
            let mut i = 0;
            while i < self.limbs.len() {
                count += self.limbs[i].count_ones();
                i += 1;
            }
            count
        }

        /// Returns the number of zeros in the binary representation of `self`.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::count_zeros`].")]
        #[inline(always)]
        pub const fn count_zeros(self) -> u32 {
            self.not_const().count_ones()
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
        /// # use i256::i256;
        /// let n = i256::MAX >> 2i32;
        /// assert_eq!(n.leading_zeros(), 3);
        ///
        /// let min = i256::MIN;
        /// assert_eq!(min.leading_zeros(), 0);
        ///
        /// let zero = i256::from_u8(0);
        /// assert_eq!(zero.leading_zeros(), 256);
        ///
        /// let max = i256::MAX;
        /// assert_eq!(max.leading_zeros(), 1);
        /// ```
        #[doc = concat!("/// See [`", stringify!($wide_t), "::leading_zeros`].")]
        #[inline]
        pub const fn leading_zeros(self) -> u32 {
            let mut count = 0;
            let mut i = 0;
            while i < Self::LIMBS && count == i as u32 * $crate::ULimb::BITS {
                count += self.limb(Self::LIMBS - i - 1).leading_zeros();
                i += 1;
            }
            count
        }

        /// Returns the number of trailing zeros in the binary representation of
        /// `self`.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::trailing_zeros`].")]
        #[inline]
        pub const fn trailing_zeros(self) -> u32 {
            let mut count = 0;
            let mut i = 0;
            while i < Self::LIMBS && count == i as u32 * $crate::ULimb::BITS {
                count += self.limb(i).trailing_zeros();
                i += 1;
            }
            count
        }

        /// Returns the number of leading ones in the binary representation of
        /// `self`.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::leading_ones`].")]
        #[inline(always)]
        pub const fn leading_ones(self) -> u32 {
            self.not_const().leading_zeros()
        }

        /// Returns the number of trailing ones in the binary representation of
        /// `self`.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::trailing_ones`].")]
        #[inline(always)]
        pub const fn trailing_ones(self) -> u32 {
            self.not_const().trailing_zeros()
        }
    };
}

/// Define a generic op. This isn't exposed to the crate just so it's done
/// internally. This is intended to be used within the crate so the `*_signed`,
/// `*_unsigned` variants can be added.
///
/// This requires the `wrapping_*` and `overflowing_*` variants to be defined,
/// as well as `div_euclid` and `rem_euclid` to be defined.
macro_rules! ops_define {
    ($t:ty, $wide_t:ty) => {
        /// Checked integer addition. Computes `self + rhs`, returning `None`
        /// if overflow occurred.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::checked_add`].")]
        #[inline(always)]
        pub const fn checked_add(self, rhs: Self) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add(rhs);
            if !overflowed {
                Some(value)
            } else {
                None
            }
        }

        /// Checked integer subtraction. Computes `self - rhs`, returning `None`
        /// if overflow occurred.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::checked_sub`].")]
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
        #[doc = concat!("/// See [`", stringify!($wide_t), "::checked_mul`].")]
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
        /// `rhs == 0` or the division results in overflow (signed only).
        #[doc = concat!("/// See [`", stringify!($wide_t), "::checked_div`].")]
        #[inline(always)]
        pub fn checked_div(self, rhs: Self) -> Option<Self> {
            if self.is_div_none(rhs) {
                None
            } else {
                Some(self.wrapping_div(rhs))
            }
        }

        /// Checked integer division. Computes `self % rhs`, returning `None`
        /// `rhs == 0` or the division results in overflow (signed only).
        #[doc = concat!("/// See [`", stringify!($wide_t), "::checked_rem`].")]
        #[inline(always)]
        pub fn checked_rem(self, rhs: Self) -> Option<Self> {
            if self.is_div_none(rhs) {
                None
            } else {
                Some(self.wrapping_rem(rhs))
            }
        }

        /// Checked Euclidean division. Computes `self.div_euclid(rhs)`,
        /// returning `None` if `rhs == 0` or the division results in
        /// overflow (signed only).
        #[doc = concat!("/// See [`", stringify!($wide_t), "::checked_div_euclid`].")]
        #[inline(always)]
        pub fn checked_div_euclid(self, rhs: Self) -> Option<Self> {
            if self.is_div_none(rhs) {
                None
            } else {
                Some(self.wrapping_div_euclid(rhs))
            }
        }

        /// Checked Euclidean modulo. Computes `self.rem_euclid(rhs)`,
        /// returning `None` if `rhs == 0` or the division results in
        /// overflow (signed only).
        #[doc = concat!("/// See [`", stringify!($wide_t), "::checked_rem_euclid`].")]
        #[inline(always)]
        pub fn checked_rem_euclid(self, rhs: Self) -> Option<Self> {
            if self.is_div_none(rhs) {
                None
            } else {
                Some(self.wrapping_rem_euclid(rhs))
            }
        }

        /// Checked shift left. Computes `self << rhs`, returning `None` if `rhs` is
        /// larger than or equal to the number of bits in `self`.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::checked_shl`].")]
        #[inline(always)]
        pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
            // Not using overflowing_shl as that's a wrapping shift
            if rhs < Self::BITS {
                Some(self.wrapping_shl(rhs))
            } else {
                None
            }
        }

        /// Checked shift right. Computes `self >> rhs`, returning `None` if `rhs`
        /// is larger than or equal to the number of bits in `self`.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::checked_shr`].")]
        #[inline(always)]
        pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
            // Not using overflowing_shr as that's a wrapping shift
            if rhs < Self::BITS {
                Some(self.wrapping_shr(rhs))
            } else {
                None
            }
        }

        /// Wrapping (modular) exponentiation. Computes `self.pow(exp)`,
        /// wrapping around at the boundary of the type.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::wrapping_pow`].")]
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

        /// Raises self to the power of `exp`, using exponentiation by squaring.
        ///
        /// Returns a tuple of the exponentiation along with a bool indicating
        /// whether an overflow happened.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::overflowing_pow`].")]
        #[inline]
        pub const fn overflowing_pow(self, mut exp: u32) -> (Self, bool) {
            if exp == 0 {
                return (Self::from_u8(1), false);
            }
            let mut base = self;
            let mut acc = Self::from_u8(1);
            let mut overflowed = false;
            let mut r: (Self, bool);

            // NOTE: The exponent can never go to 0.
            loop {
                if (exp & 1) == 1 {
                    r = acc.overflowing_mul(base);
                    // since exp!=0, finally the exp must be 1.
                    if exp == 1 {
                        r.1 |= overflowed;
                        return r;
                    }
                    acc = r.0;
                    overflowed |= r.1;
                }
                exp /= 2;
                r = base.overflowing_mul(base);
                base = r.0;
                overflowed |= r.1;
                debug_assert!(exp != 0, "logic error in exponentiation, will infinitely loop");
            }
        }

        /// Raises self to the power of `exp`, using exponentiation by squaring.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::pow`].")]
        #[inline]
        pub const fn pow(self, exp: u32) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_pow(exp)
            } else {
                self.strict_pow(exp)
            }
        }

        /// Checked exponentiation. Computes `self.pow(exp)`, returning `None`
        /// if overflow occurred.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::checked_pow`].")]
        #[inline(always)]
        pub const fn checked_pow(self, base: u32) -> Option<Self> {
            match self.overflowing_pow(base) {
                (value, false) => Some(value),
                _ => None,
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
                match self.checked_div_rem(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Div/Rem operation on a 256-bit integer.
        ///
        /// This allows storing of both the quotient and remainder without
        /// making repeated calls.
        #[inline]
        pub fn checked_div_rem(self, n: Self) -> Option<(Self, Self)> {
            if self.is_div_none(n) {
                None
            } else {
                Some(self.wrapping_div_rem(n))
            }
        }

        /// Div/Rem operation on a 256-bit integer.
        ///
        /// This allows storing of both the quotient and remainder without
        /// making repeated calls.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[inline]
        pub fn overflowing_div_rem(self, n: Self) -> ((Self, Self), bool) {
            if self.is_div_overflow(n) {
                ((self, Self::from_u8(0)), true)
            } else {
                (self.wrapping_div_rem(n), false)
            }
        }
    };
}

macro_rules! bigint_define {
    ($t:ty, $wide_t:ty) => {
        /// Calculates `self` + `rhs` + `carry` and returns a tuple containing
        /// the sum and the output carry.
        ///
        /// Performs "ternary addition" of two integer operands and a carry-in
        /// bit, and returns an output integer and a carry-out bit. This allows
        /// chaining together multiple additions to create a wider addition, and
        /// can be useful for bignum addition.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::carrying_add`].")]
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
        #[doc = concat!("/// See [`", stringify!($wide_t), "::borrowing_sub`].")]
        #[inline]
        #[must_use]
        pub const fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool) {
            let (a, b) = self.overflowing_sub(rhs);
            let (c, d) = a.overflowing_sub(Self::from_u8(borrow as u8));
            (c, b | d)
        }
    };
}

macro_rules! wrapping_define {
    ($t:ty, $wide_t:ty) => {
        // Currently a no-op
        // These are mostly custom defined for simple and larger types.
    };
}

macro_rules! overflowing_define {
    ($t:ty, $wide_t:ty) => {
        // Currently a no-op
        // These are mostly custom defined for simple and larger types.
    };
}

macro_rules! saturating_define {
    ($t:ty, $wide_t:ty) => {
        // Currently a no-op
    };
}

macro_rules! checked_define {
    ($t:ty, $wide_t:ty) => {
        /// Returns the base 2 logarithm of the number, rounded down.
        ///
        /// Returns `None` if the number is negative or zero.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::checked_ilog2`].")]
        #[inline]
        pub const fn checked_ilog2(self) -> Option<u32> {
            match self.le_const(Self::from_u8(0)) {
                true => None,
                false => Some(Self::BITS - 1 - self.leading_zeros()),
            }
        }
    };
}

macro_rules! strict_define {
    ($t:ty, $wide_t:ty) => {
        /// Strict integer addition. Computes `self + rhs`, panicking
        /// if overflow occurred.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        #[doc = concat!("/// See [`", stringify!($wide_t), "::strict_add`].")]
        #[inline]
        #[must_use]
        pub const fn strict_add(self, rhs: Self) -> Self {
            match self.checked_add(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to add with overflow"),
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
        #[doc = concat!("/// See [`", stringify!($wide_t), "::strict_sub`].")]
        #[inline]
        #[must_use]
        pub const fn strict_sub(self, rhs: Self) -> Self {
            match self.checked_sub(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to subtract with overflow"),
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
        #[doc = concat!("/// See [`", stringify!($wide_t), "::strict_mul`].")]
        #[inline]
        #[must_use]
        pub const fn strict_mul(self, rhs: Self) -> Self {
            match self.checked_mul(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to subtract with overflow"),
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
        #[doc = concat!("/// See [`", stringify!($wide_t), "::strict_pow`].")]
        #[inline]
        #[must_use]
        pub const fn strict_pow(self, rhs: u32) -> Self {
            match self.checked_pow(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to multiply with overflow"),
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
        #[doc = concat!("/// See [`", stringify!($wide_t), "::strict_shl`].")]
        #[inline]
        #[must_use]
        pub const fn strict_shl(self, rhs: u32) -> Self {
            match self.checked_shl(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to shift left with overflow"),
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
        #[doc = concat!("/// See [`", stringify!($wide_t), "::strict_shr`].")]
        #[inline]
        #[must_use]
        pub const fn strict_shr(self, rhs: u32) -> Self {
            match self.checked_shr(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to shift right with overflow"),
            }
        }
    };
}

macro_rules! unchecked_define {
    ($t:ty, $wide_t:ty) => {
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
        #[doc = concat!("/// See [`", stringify!($wide_t), "::unchecked_add`].")]
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
        #[doc = concat!("/// See [`", stringify!($wide_t), "::unchecked_sub`].")]
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
        #[doc = concat!("/// See [`", stringify!($wide_t), "::unchecked_mul`].")]
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
        #[doc = concat!("/// See [`", stringify!($wide_t), "::unchecked_shl`].")]
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
        #[doc = concat!("/// See [`", stringify!($wide_t), "::unchecked_shr`].")]
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
    };
}

macro_rules! unbounded_define {
    ($t:ty, $wide_t:ty) => {
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
    };
}

macro_rules! limb_define {
    () => {
        /// Multiply the 256-bit integer by a 64-bit unsigned factor.
        ///
        /// This allows optimizations a full multiplication cannot do.
        #[inline(always)]
        pub const fn mul_ulimb(self, n: $crate::ULimb) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_mul_ulimb(n)
            } else {
                match self.checked_mul_ulimb(n) {
                    Some(v) => v,
                    None => core::panic!("attempt to multiply with overflow"),
                }
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
        pub fn div_rem_ulimb(self, n: $crate::ULimb) -> (Self, $crate::ULimb) {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_rem_ulimb(n)
            } else {
                match self.checked_div_rem_ulimb(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Div the 256-bit integer by a 64-bit unsigned factor.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn div_ulimb(self, n: $crate::ULimb) -> Self {
            self.div_rem_ulimb(n).0
        }

        /// Rem the 256-bit integer by a 64-bit unsigned factor.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn rem_ulimb(self, n: $crate::ULimb) -> $crate::ULimb {
            self.div_rem_ulimb(n).1
        }
    };

    (@wrapping) => {
        /// Div the 256-bit integer by a 64-bit unsigned factor.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn wrapping_div_ulimb(self, n: $crate::ULimb) -> Self {
            self.wrapping_div_rem_ulimb(n).0
        }

        /// Rem the 256-bit integer by a 64-bit unsigned factor.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn wrapping_rem_ulimb(self, n: $crate::ULimb) -> $crate::ULimb {
            self.wrapping_div_rem_ulimb(n).1
        }
    };

    (@overflowing) => {
        /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline]
        pub fn overflowing_div_rem_ulimb(self, n: $crate::ULimb) -> ((Self, $crate::ULimb), bool) {
            if n == 0 {
                ((Self::MAX, 0), true)
            } else {
                (self.wrapping_div_rem_ulimb(n), false)
            }
        }

        /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn overflowing_div_ulimb(self, n: $crate::ULimb) -> (Self, bool) {
            let (value, overflowed) = self.overflowing_div_rem_ulimb(n);
            (value.0, overflowed)
        }

        /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn overflowing_rem_ulimb(self, n: $crate::ULimb) -> ($crate::ULimb, bool) {
            let (value, overflowed) = self.overflowing_div_rem_ulimb(n);
            (value.1, overflowed)
        }
    };

    (@checked) => {
        /// Multiply the 256-bit integer by a 64-bit unsigned factor.
        ///
        /// This allows optimizations a full multiplication cannot do.
        #[inline(always)]
        pub const fn checked_mul_ulimb(self, n: $crate::ULimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_mul_ulimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline]
        pub fn checked_div_rem_ulimb(self, n: $crate::ULimb) -> Option<(Self, $crate::ULimb)> {
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
        pub fn checked_div_ulimb(self, n: $crate::ULimb) -> Option<Self> {
            Some(self.checked_div_rem_ulimb(n)?.0)
        }

        /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn checked_rem_ulimb(self, n: $crate::ULimb) -> Option<$crate::ULimb> {
            Some(self.checked_div_rem_ulimb(n)?.1)
        }
    };

    (@all) => {
        limb_define!();
        limb_define!(@wrapping);
        limb_define!(@overflowing);
        limb_define!(@checked);
    };
}

macro_rules! wide_define {
    () => {
        /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn add_uwide(self, n: $crate::UWide) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_add_uwide(n)
            } else {
                match self.checked_add_uwide(n) {
                    Some(v) => v,
                    None => core::panic!("attempt to add with overflow"),
                }
            }
        }

        /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn sub_uwide(self, n: $crate::UWide) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_sub_uwide(n)
            } else {
                match self.checked_sub_uwide(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to subtract with overflow"),
                }
            }
        }

        /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
        ///
        /// This allows optimizations a full multiplication cannot do.
        #[inline(always)]
        pub const fn mul_uwide(self, n: $crate::UWide) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_mul_uwide(n)
            } else {
                match self.checked_mul_uwide(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to multiply with overflow"),
                }
            }
        }

        /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
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
        #[inline]
        pub fn div_rem_uwide(self, n: $crate::UWide) -> (Self, $crate::UWide) {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_rem_uwide(n)
            } else {
                match self.checked_div_rem_uwide(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide by zero"),
                }
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
        pub fn div_uwide(self, n: $crate::UWide) -> Self {
            self.div_rem_uwide(n).0
        }

        /// Rem the 256-bit integer by a wide, 128-bit unsigned factor.
        ///
        /// This is a convenience function: always prefer [`rem`]
        /// or [`rem_ulimb`] if possible.
        ///
        /// [`rem`]: Self::rem
        /// [`rem_ulimb`]: Self::rem_ulimb
        #[inline(always)]
        pub fn rem_uwide(self, n: $crate::UWide) -> $crate::UWide {
            self.div_rem_uwide(n).1
        }

    };

    (@wrapping) => {
        /// Div the 256-bit integer by a wide, 64-bit unsigned factor.
        ///
        /// This is a convenience function: always prefer [`wrapping_div`]
        /// or [`wrapping_div_ulimb`] if possible.
        ///
        /// # Panics
        ///
        /// This panics if the divisor is 0.
        ///
        /// [`wrapping_div`]: Self::wrapping_div
        /// [`wrapping_div_ulimb`]: Self::wrapping_div_ulimb
        #[inline(always)]
        pub fn wrapping_div_uwide(self, n: $crate::UWide) -> Self {
            self.wrapping_div_rem_uwide(n).0
        }

        /// Rem the 256-bit integer by a wide, 64-bit unsigned factor.
        ///
        /// This is a convenience function: always prefer [`wrapping_rem`]
        /// or [`wrapping_rem_ulimb`] if possible.
        ///
        /// [`wrapping_rem`]: Self::wrapping_rem
        /// [`wrapping_rem_ulimb`]: Self::wrapping_rem_ulimb
        #[inline(always)]
        pub fn wrapping_rem_uwide(self, n: $crate::UWide) -> $crate::UWide {
            self.wrapping_div_rem_uwide(n).1
        }
    };

    (@overflowing) => {
        /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
        ///
        /// This is a convenience function: always prefer [`overflowing_div_rem`]
        /// or [`overflowing_div_rem_ulimb`] if possible.
        ///
        /// [`overflowing_div_rem`]: Self::overflowing_div_rem
        /// [`overflowing_div_rem_ulimb`]: Self::overflowing_div_rem_ulimb
        #[inline]
        pub fn overflowing_div_rem_uwide(self, n: $crate::UWide) -> ((Self, $crate::UWide), bool) {
            if n == 0 {
                ((Self::MAX, 0), true)
            } else {
                (self.wrapping_div_rem_uwide(n), false)
            }
        }

        /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
        ///
        /// This is a convenience function: always prefer [`overflowing_div`]
        /// or [`overflowing_div_ulimb`] if possible.
        ///
        /// # Panics
        ///
        /// This panics if the divisor is 0.
        ///
        /// [`overflowing_div`]: Self::overflowing_div
        /// [`overflowing_div_ulimb`]: Self::overflowing_div_ulimb
        #[inline(always)]
        pub fn overflowing_div_uwide(self, n: $crate::UWide) -> (Self, bool) {
            let (value, overflowed) = self.overflowing_div_rem_uwide(n);
            (value.0, overflowed)
        }

        /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
        ///
        /// This is a convenience function: always prefer [`overflowing_rem`]
        /// or [`overflowing_rem_ulimb`] if possible.
        ///
        /// [`overflowing_rem`]: Self::overflowing_rem
        /// [`overflowing_rem_ulimb`]: Self::overflowing_rem_ulimb
        #[inline(always)]
        pub fn overflowing_rem_uwide(self, n: $crate::UWide) -> ($crate::UWide, bool) {
            let (value, overflowed) = self.overflowing_div_rem_uwide(n);
            (value.1, overflowed)
        }
    };

    (@checked) => {
        /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn checked_add_uwide(self, n: $crate::UWide) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add_uwide(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn checked_sub_uwide(self, n: $crate::UWide) -> Option<Self> {
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
        pub const fn checked_mul_uwide(self, n: $crate::UWide) -> Option<Self> {
            let (value, overflowed) = self.overflowing_mul_uwide(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
        ///
        /// This is a convenience function: always prefer [`checked_div_rem`]
        /// or [`checked_div_rem_ulimb`] if possible.
        ///
        /// [`checked_div_rem`]: Self::checked_div_rem
        /// [`checked_div_rem_ulimb`]: Self::checked_div_rem_ulimb
        #[inline]
        pub fn checked_div_rem_uwide(self, n: $crate::UWide) -> Option<(Self, $crate::UWide)> {
            if n == 0 {
                None
            } else {
                Some(self.wrapping_div_rem_uwide(n))
            }
        }

        /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
        ///
        /// This is a convenience function: always prefer [`checked_div`]
        /// or [`checked_div_ulimb`] if possible.
        ///
        /// # Panics
        ///
        /// This panics if the divisor is 0.
        ///
        /// [`checked_div`]: Self::checked_div
        /// [`checked_div_ulimb`]: Self::checked_div_ulimb
        #[inline(always)]
        pub fn checked_div_uwide(self, n: $crate::UWide) -> Option<Self> {
            Some(self.checked_div_rem_uwide(n)?.0)
        }

        /// Div/Rem the 256-bit integer by a wide, 64-bit unsigned factor.
        ///
        /// This is a convenience function: always prefer [`checked_rem`]
        /// or [`checked_rem_ulimb`] if possible.
        ///
        /// [`checked_rem`]: Self::checked_rem
        /// [`checked_rem_ulimb`]: Self::checked_rem_ulimb
        #[inline(always)]
        pub fn checked_rem_uwide(self, n: $crate::UWide) -> Option<$crate::UWide> {
            Some(self.checked_div_rem_uwide(n)?.1)
        }
    };

    (@all) => {
        wide_define!();
        wide_define!(@wrapping);
        wide_define!(@overflowing);
        wide_define!(@checked);
    };
}

macro_rules! binop_trait_define {
    ($t:ty, $trait:ident, $assign:ident, $op:ident, $op_assign:ident) => {
        impl $trait<&$t> for $t {
            type Output = <Self as $trait>::Output;

            #[inline(always)]
            fn $op(self, rhs: &Self) -> Self::Output {
                self.$op(*rhs)
            }
        }

        impl $assign for $t {
            #[inline(always)]
            fn $op_assign(&mut self, other: Self) {
                *self = self.$op(other);
            }
        }

        impl $assign<&$t> for $t {
            #[inline(always)]
            fn $op_assign(&mut self, other: &Self) {
                *self = self.$op(other);
            }
        }
    };
}

macro_rules! ref_trait_define {
    ($t:ty, $trait:ident, $op:ident $(, $args:tt:$type:ty)*) => {
        impl $trait for &$t {
            type Output = <$t as $trait>::Output;

            #[inline(always)]
            fn $op(self $(, $args: $type)*) -> Self::Output {
                $trait::$op(*self $(, $args)*)
            }
        }
    };
}

macro_rules! from_trait_define {
    ($to:ty, $from:ty, $op:ident) => {
        impl From<$from> for $to {
            #[inline(always)]
            fn from(value: $from) -> Self {
                Self::$op(value)
            }
        }
    };
}

macro_rules! binop_ref_trait_define {
    ($t:ty, $trait:ident, $op:ident) => {
        impl $trait<&$t> for $t {
            type Output = <$t as $trait>::Output;

            #[inline(always)]
            fn $op(self, other: &$t) -> Self::Output {
                $trait::$op(self, *other)
            }
        }
    };
}

macro_rules! traits_define {
    ($t:ty) => {
        impl Add for $t {
            type Output = Self;

            #[inline(always)]
            fn add(self, rhs: Self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_add(rhs)
                } else {
                    match self.checked_add(rhs) {
                        Some(v) => v,
                        _ => core::panic!("attempt to add with overflow"),
                    }
                }
            }
        }

        binop_trait_define!($t, Add, AddAssign, add, add_assign);

        impl BitAnd for $t {
            type Output = Self;

            #[inline(always)]
            fn bitand(self, rhs: Self) -> Self::Output {
                self.bitand_const(rhs)
            }
        }

        binop_trait_define!($t, BitAnd, BitAndAssign, bitand, bitand_assign);

        impl BitOr for $t {
            type Output = $t;

            #[inline(always)]
            fn bitor(self, rhs: Self) -> Self::Output {
                self.bitor_const(rhs)
            }
        }

        binop_trait_define!($t, BitOr, BitOrAssign, bitor, bitor_assign);

        impl BitXor for $t {
            type Output = Self;

            #[inline(always)]
            fn bitxor(self, rhs: Self) -> Self::Output {
                self.bitxor_const(rhs)
            }
        }

        binop_trait_define!($t, BitXor, BitXorAssign, bitxor, bitxor_assign);

        impl Div for $t {
            type Output = Self;

            #[inline(always)]
            fn div(self, rhs: Self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_div(rhs)
                } else {
                    match self.checked_div(rhs) {
                        Some(v) => v,
                        _ => core::panic!("attempt to divide with overflow"),
                    }
                }
            }
        }

        binop_trait_define!($t, Div, DivAssign, div, div_assign);

        impl Mul for $t {
            type Output = $t;

            #[inline(always)]
            fn mul(self, rhs: Self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_mul(rhs)
                } else {
                    match self.checked_mul(rhs) {
                        Some(v) => v,
                        _ => core::panic!("attempt to multiply with overflow"),
                    }
                }
            }
        }

        binop_trait_define!($t, Mul, MulAssign, mul, mul_assign);

        impl Not for $t {
            type Output = $t;

            #[inline(always)]
            fn not(self) -> Self::Output {
                self.not_const()
            }
        }

        ref_trait_define!($t, Not, not);

        impl core::cmp::Ord for $t {
            #[inline(always)]
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                self.cmp_const(*other)
            }
        }

        impl core::cmp::PartialOrd for $t {
            #[inline(always)]
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(self.cmp(other))
            }

            #[inline(always)]
            fn lt(&self, other: &Self) -> bool {
                self.lt_const(*other)
            }

            #[inline(always)]
            fn le(&self, other: &Self) -> bool {
                self.le_const(*other)
            }

            #[inline(always)]
            fn gt(&self, other: &Self) -> bool {
                self.gt_const(*other)
            }

            #[inline(always)]
            fn ge(&self, other: &Self) -> bool {
                self.ge_const(*other)
            }
        }

        impl Rem for $t {
            type Output = $t;

            #[inline(always)]
            fn rem(self, rhs: Self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_rem(rhs)
                } else {
                    match self.checked_rem(rhs) {
                        Some(v) => v,
                        _ => core::panic!("attempt to divide with overflow"),
                    }
                }
            }
        }

        binop_trait_define!($t, Rem, RemAssign, rem, rem_assign);

        impl Sub for $t {
            type Output = $t;

            #[inline(always)]
            fn sub(self, rhs: Self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_sub(rhs)
                } else {
                    match self.checked_sub(rhs) {
                        Some(v) => v,
                        _ => core::panic!("attempt to subtract with overflow"),
                    }
                }
            }
        }

        binop_trait_define!($t, Sub, SubAssign, sub, sub_assign);

        impl core::fmt::Debug for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                core::fmt::Display::fmt(self, f)
            }
        }
    };
}

pub(crate) use bigint_define;
pub(crate) use binop_ref_trait_define;
pub(crate) use binop_trait_define;
pub(crate) use bitops_define;
pub(crate) use checked_define;
pub(crate) use convert_define;
pub(crate) use extensions_define;
pub(crate) use from_trait_define;
pub(crate) use high_low_define;
pub(crate) use int_define;
pub(crate) use limb_define;
pub(crate) use ops_define;
pub(crate) use overflowing_define;
pub(crate) use ref_trait_define;
pub(crate) use saturating_define;
pub(crate) use strict_define;
pub(crate) use traits_define;
pub(crate) use unbounded_define;
pub(crate) use unchecked_define;
pub(crate) use wide_define;
pub(crate) use wrapping_define;
