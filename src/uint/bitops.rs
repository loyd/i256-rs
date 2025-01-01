//! Bitwise operations for our types.

macro_rules! define {
    (
        signed_type => $s_t:ty,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        $crate::shared::bitops::define!(
            type => $s_t,
            wide_type => $wide_t,
            see_type => $see_t
        );

        #[inline(always)]
        #[doc = $crate::shared::bitops::wrapping_shl_doc!($see_t)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_shl(self, rhs: u32) -> Self {
            let result = $crate::math::shift::left_uwide(self.to_ne_wide(), rhs % Self::BITS);
            Self::from_ne_wide(result)
        }

        #[inline(always)]
        #[doc = $crate::shared::bitops::wrapping_shr_doc!($see_t)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_shr(self, rhs: u32) -> Self {
            let result = $crate::math::shift::right_uwide(self.to_ne_wide(), rhs % Self::BITS);
            Self::from_ne_wide(result)
        }
    };
}

pub(crate) use define;
