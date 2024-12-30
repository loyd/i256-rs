//! Bitwise operations for our types.

#[rustfmt::skip]
macro_rules! define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        $crate::shared::bitops::define!(type => $u_t, wide_type => $wide_t);

        #[inline(always)]
        #[doc = $crate::shared::bitops::wrapping_shl_doc!($wide_t)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_shl(self, rhs: u32) -> Self {
            let result = $crate::math::shift::left_iwide(self.to_ne_wide(), rhs % Self::BITS);
            Self::from_ne_wide(result)
        }

        #[inline(always)]
        #[doc = $crate::shared::bitops::wrapping_shr_doc!($wide_t)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_shr(self, rhs: u32) -> Self {
            let result = $crate::math::shift::right_iwide(self.to_ne_wide(), rhs % Self::BITS);
            Self::from_ne_wide(result)
        }
    };
}

pub(crate) use define;
