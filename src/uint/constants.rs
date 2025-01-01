//! Associated constants for our types.

#[rustfmt::skip]
macro_rules! define {
    (
        bits => $bits:expr,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        $crate::shared::constants::define!(
            bits => $bits,
            wide_type => $wide_t,
            low_type => $crate::ULimb,
            high_type => $crate::ULimb,
            see_type => $see_t,
        );

        #[deprecated]
        #[inline(always)]
        #[doc = $crate::shared::constants::min_value_doc!($see_t)]
        pub const fn min_value() -> Self {
            Self::from_ne_limbs([0; Self::LIMBS])
        }

        #[deprecated]
        #[inline(always)]
        #[doc = $crate::shared::constants::max_value_doc!($see_t)]
        pub const fn max_value() -> Self {
            Self::from_ne_limbs([$crate::ULimb::MAX; Self::LIMBS])
        }

        #[doc = $crate::shared::constants::is_signed_doc!()]
        pub const IS_SIGNED: bool = false;
    };
}

pub(crate) use define;
