//! Strict arithemetic operations, which always panic on overflow.

#[rustfmt::skip]
macro_rules! define {
    (
        unsigned_type => $u_t:ty,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        $crate::shared::strict::define!(
            type => $u_t,
            wide_type => $wide_t,
            see_type => $see_t,
        );

        /// Strict addition with an unsigned integer. Computes `self + rhs`,
        /// panicking if overflow occurred.
        ///
        #[doc = $crate::shared::docs::strict_doc!(panics)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, strict_add_unsigned)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn strict_add_unsigned(self, rhs: $u_t) -> Self {
            match self.checked_add_unsigned(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to add with overflow"),
            }
        }

        /// Strict subtraction with an unsigned integer. Computes `self - rhs`,
        /// panicking if overflow occurred.
        ///
        #[doc = $crate::shared::docs::strict_doc!(panics)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, strict_sub_unsigned)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn strict_sub_unsigned(self, rhs: $u_t) -> Self {
            match self.checked_sub_unsigned(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to subtract with overflow"),
            }
        }

        /// Strict integer division. Computes `self / rhs`, panicking
        /// if overflow occurred.
        ///
        #[doc = $crate::shared::docs::strict_doc!(div-zero)]
        ///
        /// The only case where such an overflow can occur is when one divides `MIN
        /// / -1` on a signed type (where `MIN` is the negative minimal value
        /// for the type.
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

        /// Strict integer remainder. Computes `self % rhs`, panicking if
        /// the division results in overflow.
        ///
        #[doc = $crate::shared::docs::strict_doc!(div-zero)]
        ///
        /// The only case where such an overflow can occur is `x % y` for `MIN / -1`
        /// on a signed type (where `MIN` is the negative minimal value), which
        /// is invalid due to implementation artifacts.
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

        /// Strict Euclidean division. Computes `self.div_euclid(rhs)`, panicking
        /// if overflow occurred.
        ///
        #[doc = $crate::shared::docs::strict_doc!(div-zero)]
        ///
        /// The only case where such an overflow can occur is when one divides `MIN
        /// / -1` on a signed type (where `MIN` is the negative minimal value
        /// for the type); this is equivalent to `-MIN`, a positive value
        /// that is too large to represent in the type.
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

        /// Strict Euclidean remainder. Computes `self.rem_euclid(rhs)`, panicking
        /// if the division results in overflow.
        ///
        #[doc = $crate::shared::docs::strict_doc!(div-zero)]
        ///
        /// The only case where such an overflow can occur is `x % y` for `MIN / -1`
        /// on a signed type (where `MIN` is the negative minimal value), which
        /// is invalid due to implementation artifacts.
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

        /// Strict negation. Computes `-self`, panicking if `self == MIN`.
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

        /// Strict absolute value. Computes `self.abs()`, panicking if
        /// `self == MIN`.
        ///
        #[doc = $crate::shared::docs::strict_doc!(panics)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, strict_abs)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn strict_abs(self) -> Self {
            match self.checked_abs() {
                Some(v) => v,
                None => core::panic!("attempt to negate with overflow"),
            }
        }
    };
}

pub(crate) use define;
