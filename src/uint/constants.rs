//! Associated constants for our types.

#[rustfmt::skip]
macro_rules! define {
    (
        bits => $bits:expr,
        wide_type => $wide_t:ty $(,)?
    ) => {
        $crate::shared::constants::define!(
            bits => $bits,
            wide_type => $wide_t,
            low_type => $crate::ULimb,
            high_type => $crate::ULimb,
        );

        #[deprecated]
        #[inline(always)]
        #[doc = $crate::shared::constants::min_value_doc!(u128)]
        pub const fn min_value() -> Self {
            Self::from_ne_limbs([0; Self::LIMBS])
        }

        #[deprecated]
        #[inline(always)]
        #[doc = $crate::shared::constants::max_value_doc!(u128)]
        pub const fn max_value() -> Self {
            Self::from_ne_limbs([$crate::ULimb::MAX; Self::LIMBS])
        }

        #[doc = $crate::shared::constants::is_signed_doc!()]
        pub const IS_SIGNED: bool = false;
    };
}

pub(crate) use define;
