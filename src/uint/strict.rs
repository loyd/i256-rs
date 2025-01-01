//! Strict arithemetic operations, which always panic on overflow.

#[rustfmt::skip]
macro_rules! define {
    (
        signed_type => $s_t:ty,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        $crate::shared::strict::define!(
            type => $s_t,
            wide_type => $wide_t,
            see_type => $see_t,
        );

        /// Strict addition with a signed integer. Computes `self + rhs`,
        /// panicking if overflow occurred.
        ///
        #[doc = $crate::shared::docs::strict_doc!(panics)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, strict_add_signed)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn strict_add_signed(self, rhs: $s_t) -> Self {
            match self.checked_add_signed(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to negate with overflow"),
            }
        }

        /// Strict integer division. Computes `self / rhs`.
        ///
        /// Strict division on unsigned types is just normal division. There's no
        /// way overflow could ever happen. This function exists so that all
        /// operations are accounted for in the strict operations.
        ///
        #[doc = $crate::shared::docs::strict_doc!(div-zero)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, strict_div)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn strict_div(self, rhs: Self) -> Self {
            match self.checked_div(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to divide with overflow"),
            }
        }

        /// Strict integer remainder. Computes `self % rhs`.
        ///
        /// Strict remainder calculation on unsigned types is just the regular
        /// remainder calculation. There's no way overflow could ever happen.
        /// This function exists so that all operations are accounted for in the
        /// strict operations.
        ///
        #[doc = $crate::shared::docs::strict_doc!(div-zero)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, strict_rem)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn strict_rem(self, rhs: Self) -> Self {
            match self.checked_rem(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to divide with overflow"),
            }
        }

        /// Strict Euclidean division. Computes `self.div_euclid(rhs)`.
        ///
        /// Strict division on unsigned types is just normal division. There's no
        /// way overflow could ever happen. This function exists so that all
        /// operations are accounted for in the strict operations. Since, for the
        /// positive integers, all common definitions of division are equal, this
        /// is exactly equal to `self.strict_div(rhs)`.
        ///
        #[doc = $crate::shared::docs::strict_doc!(div-zero)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, strict_div_euclid)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn strict_div_euclid(self, rhs: Self) -> Self {
            match self.checked_div_euclid(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to divide with overflow"),
            }
        }

        /// Strict Euclidean modulo. Computes `self.rem_euclid(rhs)`.
        ///
        /// Strict modulo calculation on unsigned types is just the regular
        /// remainder calculation. There's no way overflow could ever happen.
        /// This function exists so that all operations are accounted for in the
        /// strict operations. Since, for the positive integers, all common
        /// definitions of division are equal, this is exactly equal to
        /// `self.strict_rem(rhs)`.
        ///
        #[doc = $crate::shared::docs::strict_doc!(div-zero)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, strict_rem_euclid)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn strict_rem_euclid(self, rhs: Self) -> Self {
            match self.checked_rem_euclid(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to divide with overflow"),
            }
        }

        /// Strict negation. Computes `-self`, panicking unless `self ==
        /// 0`.
        ///
        /// Note that negating any positive integer will overflow.
        ///
        #[doc = $crate::shared::docs::strict_doc!(panics)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, strict_neg)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn strict_neg(self) -> Self {
            match self.checked_neg() {
                Some(v) => v,
                None => core::panic!("attempt to negate with overflow"),
            }
        }
    };
}

pub(crate) use define;
