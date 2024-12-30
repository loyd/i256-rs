//! Arithematic operations which only return a value if no overflow occurs.

#[rustfmt::skip]
macro_rules! define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        $crate::shared::checked::define!(type => $u_t, wide_type => $wide_t);

        /// Checked addition with an unsigned integer. Computes `self + rhs`,
        /// returning `None` if overflow occurred.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_add_unsigned`].")]
        #[inline(always)]
        pub const fn checked_add_unsigned(self, rhs: $u_t) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add_unsigned(rhs);
            if !overflowed {
                Some(value)
            } else {
                None
            }
        }

        /// Checked subtraction with an unsigned integer. Computes `self - rhs`,
        /// returning `None` if overflow occurred.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_sub_unsigned`].")]
        #[inline(always)]
        pub const fn checked_sub_unsigned(self, rhs: $u_t) -> Option<Self> {
            let (value, overflowed) = self.overflowing_sub_unsigned(rhs);
            if !overflowed {
                Some(value)
            } else {
                None
            }
        }

        /// Checked negation. Computes `-self`, returning `None` if `self == MIN`.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_neg`].")]
        #[inline(always)]
        pub const fn checked_neg(self) -> Option<Self> {
            let (value, overflowed) = self.overflowing_neg();
            if !overflowed {
                Some(value)
            } else {
                None
            }
        }

        /// Checked absolute value. Computes `self.abs()`, returning `None` if
        /// `self == MIN`.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_abs`].")]
        #[inline(always)]
        pub const fn checked_abs(self) -> Option<Self> {
            match self.overflowing_abs() {
                (value, false) => Some(value),
                _ => None,
            }
        }

        /// Returns the logarithm of the number with respect to an arbitrary base,
        /// rounded down.
        ///
        /// Returns `None` if the number is negative or zero, or if the base is not
        /// at least 2.
        ///
        /// This method might not be optimized owing to implementation details;
        /// `checked_ilog2` can produce results more efficiently for base 2, and
        /// `checked_ilog10` can produce results more efficiently for base 10.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_ilog`].")]
        #[inline]
        pub fn checked_ilog(self, base: Self) -> Option<u32> {
            match self.le_const(Self::from_u8(0)) || base.le_const(Self::from_u8(1)) {
                true => None,
                false => Some(self.as_unsigned().ilog(base.as_unsigned())),
            }
        }

        // FIXME: Stabilize when our MSRV goes to `1.84.0+`.
        // /// Returns the square root of the number, rounded down.
        // ///
        // /// Returns `None` if `self` is negative.
        // #[inline]
        // pub const fn checked_isqrt(self) -> Option<Self> {
        //     todo!();
        // }

        // FIXME: Stabilize when our MSRV goes to `1.67.0+`.
        // /// Returns the base 10 logarithm of the number, rounded down.
        // ///
        // /// Returns `None` if the number is negative or zero.
        // #[inline]
        // pub fn checked_ilog10(self) -> Option<u32> {
        //     match self.le_const(Self::from_u8(0)) {
        //         true => None,
        //         false => Some(self.as_unsigned().ilog10()),
        //     }
        // }

        /// If `rhs` is positive, calculates the smallest value greater than or
        /// equal to `self` that is a multiple of `rhs`. If `rhs` is negative,
        /// calculates the largest value less than or equal to `self` that is a
        /// multiple of `rhs`. Returns `None` if `rhs` is zero or the operation
        /// would result in overflow.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_next_multiple_of`].")]
        #[inline]
        pub fn checked_next_multiple_of(self, rhs: Self) -> Option<Self> {
            // This would otherwise fail when calculating `r` when self == T::MIN.
            if rhs.eq_const(Self::from_i8(-1)) {
                return Some(self);
            }

            let zero = Self::from_u8(0);
            let r = self.checked_rem(rhs)?;
            let m = if (r.is_positive() & rhs.is_negative()) | (r.is_negative() & rhs.is_positive()) {
                // r + rhs cannot overflow because they have opposite signs
                r + rhs
            } else {
                r
            };

            if m.eq_const(zero) {
                Some(self)
            } else {
                // rhs - m cannot overflow because m has the same sign as rhs
                self.checked_add(rhs - m)
            }
        }
    };
}

pub(crate) use define;
