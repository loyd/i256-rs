//! Casts between primitive and signed <-> unsigned big integers.

#[rustfmt::skip]
macro_rules! define {
    (
        signed_type => $s_t:ty,
        bits => $bits:expr,
        wide_type => $wide_t:ty,
        kind => $kind:ident $(,)?
    ) => {
        $crate::shared::casts::define!(
            unsigned_type => Self,
            signed_type => $s_t,
            bits => $bits,
            kind => $kind,
        );

        /// Returns the bit pattern of `self` reinterpreted as a signed integer of
        /// the same size.
        ///
        /// This produces the same result as an `as` cast, but ensures that the
        /// bit-width remains the same.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::cast_signed`].")]
        #[inline(always)]
        pub const fn cast_signed(self) -> $s_t {
            self.as_signed()
        }
    };
}

pub(crate) use define;
