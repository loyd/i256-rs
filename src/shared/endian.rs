//! Conversion to and from native byte orders.

#[rustfmt::skip]
macro_rules! define {
    (
        type => $t:ty,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        /// The number of bytes in the type.
        const BYTES: usize = Self::BITS as usize / 8;
        const U32_LEN: usize = Self::BYTES / 4;
        const U64_LEN: usize = Self::BYTES / 8;

        /// Reverses the byte order of the integer.
        ///
        /// # Assembly
        ///
        /// This optimizes very nicely, with efficient `bswap` or `rol`
        /// implementations for each.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, swap_bytes)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn swap_bytes(&self) -> Self {
            let mut r = Self {
                limbs: [0; Self::LIMBS],
            };
            let mut i = 0;
            while i < Self::LIMBS {
                r.limbs[i] = self.limbs[Self::LIMBS - 1 - i].swap_bytes();
                i += 1;
            }
            r
        }

        /// Reverses the order of bits in the integer. The least significant
        /// bit becomes the most significant bit, second least-significant bit
        /// becomes second most-significant bit, etc.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, reverse_bits)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn reverse_bits(&self) -> Self {
            let mut r = Self {
                limbs: [0; Self::LIMBS],
            };
            let mut i = 0;
            while i < Self::LIMBS {
                r.limbs[i] = self.limbs[Self::LIMBS - 1 - i].reverse_bits();
                i += 1;
            }
            r
        }

        /// Converts an integer from big endian to the target's endianness.
        ///
        /// On big endian this is a no-op. On little endian the bytes are
        /// swapped.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, from_be)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
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
        #[doc = $crate::shared::docs::primitive_doc!($see_t, from_le)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
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
        #[doc = $crate::shared::docs::primitive_doc!($see_t, to_be)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
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
        #[doc = $crate::shared::docs::primitive_doc!($see_t, to_le)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_le(self) -> Self {
            if cfg!(target_endian = "little") {
                self
            } else {
                self.swap_bytes()
            }
        }

        /// Returns the memory representation of this integer as a byte array in
        /// big-endian (network) byte order.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, to_be_bytes)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_be_bytes(self) -> [u8; Self::BYTES] {
            self.to_be().to_ne_bytes()
        }

        /// Returns the memory representation of this integer as a byte array in
        /// little-endian byte order.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, to_le_bytes)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_le_bytes(self) -> [u8; Self::BYTES] {
            self.to_le().to_ne_bytes()
        }

        /// Returns the memory representation of this integer as a byte array in
        /// native byte order.
        ///
        /// As the target platform's native endianness is used, portable code
        /// should use [`to_be_bytes`] or [`to_le_bytes`], as appropriate,
        /// instead.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, to_ne_bytes)]
        ///
        /// [`to_be_bytes`]: Self::to_be_bytes
        /// [`to_le_bytes`]: Self::to_le_bytes
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_ne_bytes(self) -> [u8; Self::BYTES] {
            // SAFETY: plain old data
            unsafe {
                core::mem::transmute::<[$crate::ULimb; Self::LIMBS], [u8; Self::BYTES]>(self.limbs)
            }
        }

        /// Creates a native endian integer value from its representation
        /// as a byte array in big endian.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, from_be_bytes)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_be_bytes(bytes: [u8; Self::BYTES]) -> Self {
            Self::from_ne_bytes(bytes).to_be()
        }

        /// Creates a native endian integer value from its representation
        /// as a byte array in little endian.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, from_le_bytes)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_le_bytes(bytes: [u8; Self::BYTES]) -> Self {
            Self::from_ne_bytes(bytes).to_le()
        }

        /// Creates a native endian integer value from its memory representation
        /// as a byte array in native endianness.
        ///
        /// As the target platform's native endianness is used, portable code
        /// likely wants to use [`from_be_bytes`] or [`from_le_bytes`], as
        /// appropriate instead.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, from_ne_bytes)]
        ///
        /// [`from_be_bytes`]: Self::from_be_bytes
        /// [`from_le_bytes`]: Self::from_le_bytes
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_ne_bytes(bytes: [u8; Self::BYTES]) -> Self {
            // SAFETY: plain old data
            let limbs = unsafe {
                core::mem::transmute::<[u8; Self::BYTES], [$crate::ULimb; Self::LIMBS]>(bytes)
            };
            Self::from_ne_limbs(limbs)
        }

        /// Returns the memory representation of this as a series of limbs in
        /// big-endian (network) byte order.
        ///
        /// The value of each limb stays the same, however, the order that each
        /// is stored within the buffer is in big-endian order.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_be_limbs(self) -> [$crate::ULimb; Self::LIMBS] {
            if cfg!(target_endian = "little") {
                swap_array!(self.to_ne_limbs())
            } else {
                self.to_ne_limbs()
            }
        }

        /// Returns the memory representation of this as a series of limbs in
        /// little-endian byte order.
        ///
        /// The value of each limb stays the same, however, the order that each
        /// is stored within the buffer is in little-endian order.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_le_limbs(self) -> [$crate::ULimb; Self::LIMBS] {
            if cfg!(target_endian = "little") {
                self.to_ne_limbs()
            } else {
                swap_array!(self.to_ne_limbs())
            }
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
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_ne_limbs(self) -> [$crate::ULimb; Self::LIMBS] {
            self.limbs
        }

        /// Creates a native endian integer value from its representation
        /// as limbs in big endian.
        ///
        /// The value of each limb stays the same, however, the order that each
        /// is stored within the buffer as if it was from big-endian order.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_be_limbs(limbs: [$crate::ULimb; Self::LIMBS]) -> Self {
            if cfg!(target_endian = "big") {
                Self::from_ne_limbs(limbs)
            } else {
                Self::from_ne_limbs(swap_array!(limbs))
            }
        }

        /// Creates a native endian integer value from its representation
        /// as limbs in little endian.
        ///
        /// The value of each limb stays the same, however, the order that each
        /// is stored within the buffer as if it was from little-endian order.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_le_limbs(limbs: [$crate::ULimb; Self::LIMBS]) -> Self {
            if cfg!(target_endian = "big") {
                Self::from_ne_limbs(swap_array!(limbs))
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
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_ne_limbs(limbs: [$crate::ULimb; Self::LIMBS]) -> Self {
            assert!(Self::BITS % 128 == 0, "must have a multiple of 128 for our size.");
            Self {
                limbs,
            }
        }

        /// Returns the memory representation of this as a series of wide in
        /// big-endian (network) byte order.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_be_wide(self) -> [$crate::UWide; Self::WIDE] {
            if cfg!(target_endian = "little") {
                swap_array!(self.to_ne_wide())
            } else {
                self.to_ne_wide()
            }
        }

        /// Returns the memory representation of this as a series of wide in
        /// little-endian byte order.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_le_wide(self) -> [$crate::UWide; Self::WIDE] {
            if cfg!(target_endian = "little") {
                self.to_ne_wide()
            } else {
                swap_array!(self.to_ne_wide())
            }
        }

        /// Returns the memory representation of this as a series of wide types.
        ///
        /// As the target platform's native endianness is used, portable code
        /// should use [`to_be_wide`] or [`to_le_wide`], as appropriate,
        /// instead.
        ///
        /// [`to_be_wide`]: Self::to_be_wide
        /// [`to_le_wide`]: Self::to_le_wide
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_ne_wide(self) -> [$crate::UWide; Self::WIDE] {
            let bytes = self.to_ne_bytes();
            // SAFETY: plain old data
            unsafe {
                core::mem::transmute::<[u8; Self::BYTES], [$crate::UWide; Self::WIDE]>(bytes)
            }
        }

        /// Creates a native endian integer value from its representation
        /// as a wide type in big endian.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_be_wide(wide: [$crate::UWide; Self::WIDE]) -> Self {
            if cfg!(target_endian = "big") {
                Self::from_ne_wide(wide)
            } else {
                Self::from_ne_wide(swap_array!(wide))
            }
        }

        /// Creates a native endian integer value from its representation
        /// as a wide type in little endian.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_le_wide(wide: [$crate::UWide; Self::WIDE]) -> Self {
            if cfg!(target_endian = "big") {
                Self::from_ne_wide(swap_array!(wide))
            } else {
                Self::from_ne_wide(wide)
            }
        }

        /// Creates a native endian integer value from its memory representation
        /// as a wide type in native endianness.
        ///
        /// As the target platform's native endianness is used, portable code
        /// likely wants to use [`from_be_wide`] or [`from_le_wide`], as
        /// appropriate instead.
        ///
        /// [`from_be_wide`]: Self::from_be_wide
        /// [`from_le_wide`]: Self::from_le_wide
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_ne_wide(wide: [$crate::UWide; Self::WIDE]) -> Self {
            // SAFETY: plain old data
            let bytes = unsafe {
                core::mem::transmute::<[$crate::UWide; Self::WIDE], [u8; Self::BYTES]>(wide)
            };
            Self::from_ne_bytes(bytes)
        }

        /// Returns the memory representation of this as a series of `u32` digits
        /// in big-endian order.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_be_u32(self) -> [u32; Self::U32_LEN] {
            if cfg!(target_endian = "little") {
                swap_array!(self.to_ne_u32())
            } else {
                self.to_ne_u32()
            }
        }

        /// Returns the memory representation of this as a series of `u32` digits
        /// in litte-endian order.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_le_u32(self) -> [u32; Self::U32_LEN] {
            if cfg!(target_endian = "little") {
                self.to_ne_u32()
            } else {
                swap_array!(self.to_ne_u32())
            }
        }

        /// Returns the memory representation of this as a series of `u32`.
        ///
        /// As the target platform's native endianness is used, portable code
        /// should use [`to_be_u32`] or [`to_le_u32`], as appropriate,
        /// instead.
        ///
        /// [`to_be_u32`]: Self::to_be_u32
        /// [`to_le_u32`]: Self::to_le_u32
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_ne_u32(self) -> [u32; Self::U32_LEN] {
            let bytes = self.to_ne_bytes();
            // SAFETY: plain old data
            unsafe {
                core::mem::transmute::<[u8; Self::BYTES], [u32; Self::U32_LEN]>(bytes)
            }
        }

        /// Creates a native endian integer value from its representation
        /// as `u32` elements in big-endian.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_be_u32(value: [u32; Self::U32_LEN]) -> Self {
            if cfg!(target_endian = "big") {
                Self::from_ne_u32(value)
            } else {
                Self::from_ne_u32(swap_array!(value))
            }
        }

        /// Creates a native endian integer value from its representation
        /// as `u32` elements in little-endian.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_le_u32(value: [u32; Self::U32_LEN]) -> Self {
            if cfg!(target_endian = "big") {
                Self::from_ne_u32(swap_array!(value))
            } else {
                Self::from_ne_u32(value)
            }
        }

        /// Creates a native endian integer value from its memory representation
        /// as `u32` in native endianness.
        ///
        /// As the target platform's native endianness is used, portable code
        /// likely wants to use [`from_be_u32`] or [`from_le_u32`], as
        /// appropriate instead.
        ///
        /// [`from_be_u32`]: Self::from_be_u32
        /// [`from_le_u32`]: Self::from_le_u32
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_ne_u32(value: [u32; Self::U32_LEN]) -> Self {
            // SAFETY: plain old data
            let bytes = unsafe {
                core::mem::transmute::<[u32; Self::U32_LEN], [u8; Self::BYTES]>(value)
            };
            Self::from_ne_bytes(bytes)
        }

        /// Returns the memory representation of this as a series of `u64` digits
        /// in big-endian order.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_be_u64(self) -> [u64; Self::U64_LEN] {
            if cfg!(target_endian = "little") {
                swap_array!(self.to_ne_u64())
            } else {
                self.to_ne_u64()
            }
        }

        /// Returns the memory representation of this as a series of `u64` digits
        /// in litte-endian order.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_le_u64(self) -> [u64; Self::U64_LEN] {
            if cfg!(target_endian = "little") {
                self.to_ne_u64()
            } else {
                swap_array!(self.to_ne_u64())
            }
        }

        /// Returns the memory representation of this as a series of `u64`.
        ///
        /// As the target platform's native endianness is used, portable code
        /// should use [`to_be_u64`] or [`to_le_u64`], as appropriate,
        /// instead.
        ///
        /// [`to_be_u64`]: Self::to_be_u64
        /// [`to_le_u64`]: Self::to_le_u64
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn to_ne_u64(self) -> [u64; Self::U64_LEN] {
            let bytes = self.to_ne_bytes();
            // SAFETY: plain old data
            unsafe {
                core::mem::transmute::<[u8; Self::BYTES], [u64; Self::U64_LEN]>(bytes)
            }
        }

        /// Creates a native endian integer value from its representation
        /// as `u64` elements in big-endian.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_be_u64(value: [u64; Self::U64_LEN]) -> Self {
            if cfg!(target_endian = "big") {
                Self::from_ne_u64(value)
            } else {
                Self::from_ne_u64(swap_array!(value))
            }
        }

        /// Creates a native endian integer value from its representation
        /// as `u64` elements in little-endian.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_le_u64(value: [u64; Self::U64_LEN]) -> Self {
            if cfg!(target_endian = "big") {
                Self::from_ne_u64(swap_array!(value))
            } else {
                Self::from_ne_u64(value)
            }
        }

        /// Creates a native endian integer value from its memory representation
        /// as `u64` in native endianness.
        ///
        /// As the target platform's native endianness is used, portable code
        /// likely wants to use [`from_be_u64`] or [`from_le_u64`], as
        /// appropriate instead.
        ///
        /// [`from_be_u64`]: Self::from_be_u64
        /// [`from_le_u64`]: Self::from_le_u64
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn from_ne_u64(value: [u64; Self::U64_LEN]) -> Self {
            // SAFETY: plain old data
            let bytes = unsafe {
                core::mem::transmute::<[u64; Self::U64_LEN], [u8; Self::BYTES]>(value)
            };
            Self::from_ne_bytes(bytes)
        }
    };
}

pub(crate) use define;
