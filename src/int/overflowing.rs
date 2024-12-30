//! Overflowing mathmetical operations, which wrap and return if it overflowed.

#[rustfmt::skip]
macro_rules! define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        $crate::shared::overflowing::define!(type => $u_t, wide_type => $wide_t);

        /// Calculates `self` + `rhs`.
        ///
        /// Returns a tuple of the addition along with a boolean indicating
        /// whether an arithmetic overflow would occur. If an overflow would have
        /// occurred then the wrapped value is returned.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_add`].")]
        #[inline(always)]
        pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
            let lhs = self.to_ne_limbs();
            let rhs = rhs.to_ne_limbs();
            let (limbs, overflowed) = $crate::math::add::overflowing_signed(&lhs, &rhs);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Calculates `self` - `rhs`.
        ///
        /// Returns a tuple of the subtraction along with a boolean indicating
        /// whether an arithmetic overflow would occur. If an overflow would
        /// have occurred then the wrapped value is returned.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_sub`].")]
        #[inline(always)]
        pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
            let lhs = self.to_ne_limbs();
            let rhs = rhs.to_ne_limbs();
            let (limbs, overflowed) = $crate::math::sub::overflowing_signed(&lhs, &rhs);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Calculates `self` + `rhs` with an unsigned `rhs`.
        ///
        /// Returns a tuple of the addition along with a boolean indicating
        /// whether an arithmetic overflow would occur. If an overflow would
        /// have occurred then the wrapped value is returned.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_add_unsigned`].")]
        #[inline(always)]
        pub const fn overflowing_add_unsigned(self, rhs: $u_t) -> (Self, bool) {
            let rhs = rhs.as_signed();
            let (res, overflowed) = self.overflowing_add(rhs);
            (res, overflowed ^ rhs.is_negative())
        }

        /// Calculates `self` - `rhs` with an unsigned `rhs`.
        ///
        /// Returns a tuple of the subtraction along with a boolean indicating
        /// whether an arithmetic overflow would occur. If an overflow would
        /// have occurred then the wrapped value is returned.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_sub_unsigned`].")]
        #[inline(always)]
        pub const fn overflowing_sub_unsigned(self, rhs: $u_t) -> (Self, bool) {
            let rhs = rhs.as_signed();
            let (res, overflowed) = self.overflowing_sub(rhs);
            (res, overflowed ^ rhs.is_negative())
        }

        /// Calculates the multiplication of `self` and `rhs`.
        ///
        /// Returns a tuple of the multiplication along with a boolean
        /// indicating whether an arithmetic overflow would occur. If an
        /// overflow would have occurred then the wrapped value is returned.
        ///
        /// This in worst case 10 `mul`, 20 `add`, and 9 `sub` instructions,
        /// significantly slower than the wrapping variant.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_mul`].")]
        #[inline(always)]
        pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
            let lhs = self.to_ne_limbs();
            let rhs = rhs.to_ne_limbs();
            let (limbs, overflowed) = $crate::math::mul::overflowing_signed(&lhs, &rhs);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Calculates the divisor when `self` is divided by `rhs`.
        ///
        /// Returns a tuple of the divisor along with a boolean indicating whether
        /// an arithmetic overflow would occur. If an overflow would occur then
        /// self is returned.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_div`].")]
        #[inline(always)]
        pub fn overflowing_div(self, rhs: Self) -> (Self, bool) {
            if self.is_div_overflow(rhs) {
                (self, true)
            } else {
                (self.wrapping_div(rhs), false)
            }
        }

        /// Calculates the quotient of Euclidean division `self.div_euclid(rhs)`.
        ///
        /// Returns a tuple of the divisor along with a boolean indicating whether
        /// an arithmetic overflow would occur. If an overflow would occur then
        /// `self` is returned.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_div_euclid`].")]
        #[inline(always)]
        pub fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) {
            if self.is_div_overflow(rhs) {
                (self, true)
            } else {
                (self.wrapping_div_euclid(rhs), false)
            }
        }

        /// Calculates the remainder when `self` is divided by `rhs`.
        ///
        /// Returns a tuple of the remainder after dividing along with a boolean
        /// indicating whether an arithmetic overflow would occur. If an
        /// overflow would occur then 0 is returned.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_rem`].")]
        #[inline(always)]
        pub fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
            if self.is_div_overflow(rhs) {
                (Self::from_u8(0), self.eq_const(Self::MIN))
            } else {
                (self.wrapping_rem(rhs), false)
            }
        }

        /// Overflowing Euclidean remainder. Calculates `self.rem_euclid(rhs)`.
        ///
        /// Returns a tuple of the remainder after dividing along with a boolean
        /// indicating whether an arithmetic overflow would occur. If an
        /// overflow would occur then 0 is returned.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_rem_euclid`].")]
        #[inline(always)]
        pub fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) {
            if self.is_div_overflow(rhs) {
                (Self::from_u8(0), self.eq_const(Self::MIN))
            } else {
                (self.wrapping_rem_euclid(rhs), false)
            }
        }

        /// Negates self, overflowing if this is equal to the minimum value.
        ///
        /// Returns a tuple of the negated version of self along with a boolean
        /// indicating whether an overflow happened. If `self` is the minimum
        /// value (e.g., `i32::MIN` for values of type `i32`), then the
        /// minimum value will be returned again and `true` will be returned for an
        /// overflow happening.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_neg`].")]
        #[inline(always)]
        pub const fn overflowing_neg(self) -> (Self, bool) {
            if self.eq_const(Self::MIN) {
                (Self::MIN, true)
            } else {
                (self.wrapping_neg(), false)
            }
        }

        /// Shifts self left by `rhs` bits.
        ///
        /// Returns a tuple of the shifted version of self along with a boolean
        /// indicating whether the shift value was larger than or equal to the
        /// number of bits. If the shift value is too large, then value is
        /// masked (N-1) where N is the number of bits, and this value is then used
        /// to perform the shift.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_shl`].")]
        #[inline(always)]
        pub const fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
            (self.wrapping_shl(rhs), rhs >= Self::BITS)
        }

        /// Shifts self right by `rhs` bits.
        ///
        /// Returns a tuple of the shifted version of self along with a boolean
        /// indicating whether the shift value was larger than or equal to the
        /// number of bits. If the shift value is too large, then value is
        /// masked (N-1) where N is the number of bits, and this value is then used
        /// to perform the shift.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_shr`].")]
        #[inline(always)]
        pub const fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
            (self.wrapping_shr(rhs), rhs >= Self::BITS)
        }

        /// Computes the absolute value of `self`.
        ///
        /// Returns a tuple of the absolute version of self along with a boolean
        /// indicating whether an overflow happened.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_abs`].")]
        #[inline(always)]
        pub const fn overflowing_abs(self) -> (Self, bool) {
            match self.is_negative() {
                true => self.overflowing_neg(),
                false => (self, false),
            }
        }
    };
}

pub(crate) use define;
