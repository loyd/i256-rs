//! Overflowing mathmetical operations, which saturate max or min on overflow.

#[rustfmt::skip]
macro_rules! define {
    (
        unsigned_type => $u_t:ty,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        $crate::shared::saturating::define!(
            type => $u_t,
            wide_type => $wide_t,
            see_type => $see_t,
        );

        /// Saturating integer addition. Computes `self + rhs`, saturating at the
        /// numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, saturating_add)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_add(self, rhs: Self) -> Self {
            match self.checked_add(rhs) {
                Some(value) => value,
                None if self.is_negative() => Self::MIN,
                None => Self::MAX,
            }
        }

        /// Saturating addition with an unsigned integer. Computes `self + rhs`,
        /// saturating at the numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, saturating_add_unsigned)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_add_unsigned(self, rhs: $u_t) -> Self {
            // Overflow can only happen at the upper bound
            // We cannot use `unwrap_or` here because it is not `const`
            match self.checked_add_unsigned(rhs) {
                Some(x) => x,
                None => Self::MAX,
            }
        }

        /// Saturating integer subtraction. Computes `self - rhs`, saturating at the
        /// numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, saturating_sub)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_sub(self, rhs: Self) -> Self {
            match self.checked_sub(rhs) {
                Some(value) => value,
                None if self.is_negative() => Self::MIN,
                None => Self::MAX,
            }
        }

        /// Saturating subtraction with an unsigned integer. Computes `self - rhs`,
        /// saturating at the numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, saturating_sub_unsigned)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_sub_unsigned(self, rhs: $u_t) -> Self {
            // Overflow can only happen at the lower bound
            // We cannot use `unwrap_or` here because it is not `const`
            match self.checked_sub_unsigned(rhs) {
                Some(x) => x,
                None => Self::MIN,
            }
        }

        /// Saturating integer negation. Computes `-self`, returning `MAX` if `self
        /// == MIN` instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, saturating_neg)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_neg(self) -> Self {
            Self::from_u8(0).saturating_sub(self)
        }

        /// Saturating absolute value. Computes `self.abs()`, returning `MAX` if
        /// `self == MIN` instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, saturating_abs)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_abs(self) -> Self {
            match self.checked_abs() {
                Some(value) => value,
                None => Self::MAX,
            }
        }

        /// Saturating integer multiplication. Computes `self * rhs`, saturating at
        /// the numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, saturating_mul)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_mul(self, rhs: Self) -> Self {
            match self.checked_mul(rhs) {
                Some(x) => x,
                None => {
                    if self.is_negative() == rhs.is_negative() {
                        Self::MAX
                    } else {
                        Self::MIN
                    }
                },
            }
        }

        /// Saturating integer division. Computes `self / rhs`, saturating at the
        /// numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, saturating_div)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        #[inline(always)]
        pub fn saturating_div(self, rhs: Self) -> Self {
            match self.overflowing_div(rhs) {
                (result, false) => result,
                (_result, true) => Self::MAX, // MIN / -1 is the only possible saturating overflow
            }
        }

        /// Saturating integer exponentiation. Computes `self.pow(exp)`,
        /// saturating at the numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, saturating_pow)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_pow(self, exp: u32) -> Self {
            match self.checked_pow(exp) {
                Some(x) => x,
                None if self.lt_const(Self::from_u8(0)) && exp % 2 == 1 => Self::MIN,
                None => Self::MAX,
            }
        }
    };
}

pub(crate) use define;
