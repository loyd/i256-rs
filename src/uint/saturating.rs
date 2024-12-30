//! Overflowing mathmetical operations, which saturate max or min on overflow.

#[rustfmt::skip]
macro_rules! define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        $crate::shared::saturating::define!(type => $s_t, wide_type => $wide_t);

        /// Saturating integer addition. Computes `self + rhs`, saturating at
        /// the numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u128, saturating_add)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_add(self, rhs: Self) -> Self {
            match self.checked_add(rhs) {
                Some(v) => v,
                None => Self::MAX,
            }
        }

        /// Saturating addition with a signed integer. Computes `self + rhs`,
        /// saturating at the numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u128, saturating_add_signed)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_add_signed(self, rhs: $s_t) -> Self {
            let is_negative = rhs.is_negative();
            let (r, overflowed) = self.overflowing_add(Self::from_signed(rhs));
            if overflowed == is_negative {
                r
            } else if overflowed {
                Self::MAX
            } else {
                Self::MIN
            }
        }

        /// Saturating integer subtraction. Computes `self - rhs`, saturating
        /// at the numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u128, saturating_sub)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_sub(self, rhs: Self) -> Self {
            match self.checked_sub(rhs) {
                Some(v) => v,
                None => Self::MIN,
            }
        }

        /// Saturating integer multiplication. Computes `self * rhs`,
        /// saturating at the numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u128, saturating_mul)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_mul(self, rhs: Self) -> Self {
            match self.checked_mul(rhs) {
                Some(v) => v,
                None => Self::MAX,
            }
        }

        /// Saturating integer division. Computes `self / rhs`, saturating at the
        /// numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u128, saturating_div)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn saturating_div(self, rhs: Self) -> Self {
            // on unsigned types, there is no overflow in integer division
            self.wrapping_div(rhs)
        }

        /// Saturating integer exponentiation. Computes `self.pow(exp)`,
        /// saturating at the numeric bounds instead of overflowing.
        ///
        #[doc = $crate::shared::docs::primitive_doc!(u128, saturating_pow)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn saturating_pow(self, exp: u32) -> Self {
            match self.checked_pow(exp) {
                Some(x) => x,
                None => Self::MAX,
            }
        }
    };
}

pub(crate) use define;
