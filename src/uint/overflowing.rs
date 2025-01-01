//! Overflowing mathmetical operations, which wrap and return if it
//! overflowed.

#[rustfmt::skip]
macro_rules! define {
    (
        signed_type => $s_t:ty,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        $crate::shared::overflowing::define!(
            type => $s_t,
            wide_type => $wide_t,
            see_type => $see_t,
        );

        /// Calculates `self` + `rhs`.
        ///
        /// Returns a tuple of the addition along with a boolean indicating
        /// whether an arithmetic overflow would occur. If an overflow would
        /// have occurred then the wrapped value is returned.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, overflowing_add)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
            let lhs = self.to_ne_limbs();
            let rhs = rhs.to_ne_limbs();
            let (limbs, overflowed) = $crate::math::add::overflowing_unsigned(&lhs, &rhs);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Calculates `self` + `rhs` with a signed `rhs`.
        ///
        /// Returns a tuple of the addition along with a boolean indicating
        /// whether an arithmetic overflow would occur. If an overflow would
        /// have occurred then the wrapped value is returned.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, overflowing_add_signed)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_add_signed(self, rhs: $s_t) -> (Self, bool) {
            let is_negative = rhs.is_negative();
            let (r, overflowed) = self.overflowing_add(Self::from_signed(rhs));
            (r, overflowed ^ is_negative)
        }

        /// Calculates `self` - `rhs`.
        ///
        /// Returns a tuple of the subtraction along with a boolean indicating
        /// whether an arithmetic overflow would occur. If an overflow would
        /// have occurred then the wrapped value is returned.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, overflowing_sub)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
            let lhs = self.to_ne_limbs();
            let rhs = rhs.to_ne_limbs();
            let (limbs, overflowed) = $crate::math::sub::overflowing_unsigned(&lhs, &rhs);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Calculates `self` - `rhs` with a signed `rhs`
        ///
        /// Returns a tuple of the subtraction along with a boolean indicating
        /// whether an arithmetic overflow would occur. If an overflow would
        /// have occurred then the wrapped value is returned.
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_sub_signed(self, rhs: $s_t) -> (Self, bool) {
            let (res, overflow) = self.overflowing_sub(rhs.as_unsigned());
            (res, overflow ^ (rhs.is_negative()))
        }

        /// Calculates the multiplication of `self` and `rhs`.
        ///
        /// Returns a tuple of the multiplication along with a boolean
        /// indicating whether an arithmetic overflow would occur. If an
        /// overflow would have occurred then the wrapped value is returned.
        ///
        /// Many different algorithms were attempted, with a soft [`mulx`] approach
        /// (1), a flat, fixed-width long multiplication (2), and a
        /// short-circuiting long multiplication (3). Algorithm (3) had the best
        /// performance for 128-bit multiplication, however, algorithm (1) was
        /// better for smaller type sizes.
        ///
        /// This also optimized much better when multiplying by a single or a
        /// half-sized item: rather than using 4 limbs, if we're multiplying
        /// `(u128, u128) * u128`, we can use 2 limbs for the right operand, and
        /// for `(u128, u128) * u64`, only 1 limb.
        ///
        /// # Assembly
        ///
        /// The analysis here is practically identical to that of [`wrapping_mul`].
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, overflowing_mul)]
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        /// [`wrapping_mul`]: Self::wrapping_mul
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
            let lhs = self.to_ne_limbs();
            let rhs = rhs.to_ne_limbs();
            let (limbs, overflowed) = $crate::math::mul::overflowing_unsigned(&lhs, &rhs);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Calculates the divisor when `self` is divided by `rhs`.
        ///
        /// Returns a tuple of the divisor along with a boolean indicating
        /// whether an arithmetic overflow would occur. Note that for unsigned
        /// integers overflow never occurs, so the second value is always
        /// `false`.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, overflowing_div)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_div(self, rhs: Self) -> (Self, bool) {
            (self.wrapping_div(rhs), false)
        }

        /// Calculates the quotient of Euclidean division `self.div_euclid(rhs)`.
        ///
        /// Returns a tuple of the divisor along with a boolean indicating
        /// whether an arithmetic overflow would occur. Note that for unsigned
        /// integers overflow never occurs, so the second value is always
        /// `false`.
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this
        /// is exactly equal to `self.overflowing_div(rhs)`.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, overflowing_div_euclid)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) {
            self.overflowing_div(rhs)
        }

        /// Calculates the remainder when `self` is divided by `rhs`.
        ///
        /// Returns a tuple of the remainder after dividing along with a boolean
        /// indicating whether an arithmetic overflow would occur. Note that for
        /// unsigned integers overflow never occurs, so the second value is
        /// always `false`.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, overflowing_rem)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
            (self.wrapping_rem(rhs), false)
        }

        /// Calculates the remainder `self.rem_euclid(rhs)` as if by Euclidean
        /// division.
        ///
        /// Returns a tuple of the modulo after dividing along with a boolean
        /// indicating whether an arithmetic overflow would occur. Note that for
        /// unsigned integers overflow never occurs, so the second value is
        /// always `false`.
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this operation
        /// is exactly equal to `self.overflowing_rem(rhs)`.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, overflowing_rem_euclid)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) {
            self.overflowing_rem(rhs)
        }
    };
}

pub(crate) use define;
