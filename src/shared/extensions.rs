//! Custom integer extensions for ergonomics.

macro_rules! define {
    (high_type => $hi_t:ty $(,)?) => {
        /// Get if the integer is even.
        #[inline(always)]
        pub const fn is_even(&self) -> bool {
            self.get_limb(0) % 2 == 0
        }

        /// Get if the integer is odd.
        #[inline(always)]
        pub const fn is_odd(&self) -> bool {
            !self.is_even()
        }

        /// Get the limb indexing from the least-significant order.
        #[inline(always)]
        pub const fn get_limb(&self, index: usize) -> $crate::ULimb {
            ne_index!(self.limbs[index])
        }

        /// Get the wide value indexing from the least-significant order.
        ///
        /// This optimizes extremely well, if the index is known ahead of time
        /// into 2 `mov` instructions, that is, as efficient as can be.
        #[inline(always)]
        pub const fn get_wide(&self, index: usize) -> $crate::UWide {
            const LIMB: usize = core::mem::size_of::<$crate::ULimb>();
            const WIDE: usize = core::mem::size_of::<$crate::UWide>();
            assert!(WIDE / LIMB == 2);
            assert!(index < Self::WIDE, "index must be less than the total wide values");

            // NOTE: We can just grab the bytes based on the indexes,
            // and break it into 2 limbs and then build it in native
            // ending order.
            let offset = if cfg!(target_endian = "big") {
                Self::LIMBS - 2 * (index + 1)
            } else {
                2 * index
            };
            let lo = self.limbs[offset].to_ne_bytes();
            let hi = self.limbs[offset + 1].to_ne_bytes();

            // convert as via a transmute to our wide type and transmute
            // SAFETY: plain old data
            let bytes = unsafe { core::mem::transmute::<[[u8; LIMB]; 2], [u8; WIDE]>([lo, hi]) };
            $crate::UWide::from_ne_bytes(bytes)
        }

        /// Get the least significant limb in the buiffer.
        #[inline(always)]
        pub const fn least_significant_limb(&self) -> $crate::ULimb {
            self.get_limb(0)
        }

        /// Get the most significant limb in the buiffer.
        #[inline(always)]
        pub const fn most_significant_limb(&self) -> $hi_t {
            self.get_limb(Self::LIMBS - 1) as $hi_t
        }
    };
}

pub(crate) use define;
