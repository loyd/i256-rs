//! Arithematic operations which only return a value if no overflow occurs.

#[rustfmt::skip]
macro_rules! define {
    (
        signed_type => $s_t:ty,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        $crate::shared::checked::define!(
            type => $s_t,
            wide_type => $wide_t,
            see_type => $see_t,
        );

        /// Checked addition with a signed integer. Computes `self + rhs`,
        /// returning `None` if overflow occurred.
        #[doc = $crate::shared::docs::primitive_doc!($see_t, checked_add_signed)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_add_signed(self, rhs: $s_t) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add_signed(rhs);
            if !overflowed {
                Some(value)
            } else {
                None
            }
        }

        /// Checked negation. Computes `-self`, returning `None` unless `self ==
        /// 0`.
        ///
        /// Note that negating any positive integer will overflow.
        #[doc = $crate::shared::docs::primitive_doc!($see_t, checked_neg)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_neg(self) -> Option<Self> {
            if self.eq_const(Self::MIN) {
                Some(self)
            } else {
                None
            }
        }

        /// Returns the logarithm of the number with respect to an arbitrary base,
        /// rounded down.
        ///
        /// Returns `None` if the number is zero, or if the base is not at least 2.
        ///
        /// This method might not be optimized owing to implementation details;
        /// `checked_ilog2` can produce results more efficiently for base 2, and
        /// `checked_ilog10` can produce results more efficiently for base 10.
        #[doc = $crate::shared::docs::primitive_doc!($see_t, checked_ilog)]
        #[inline(always)]
        pub fn checked_ilog(self, base: Self) -> Option<u32> {
            let zero = Self::from_u8(0);
            if self == zero || base <= zero || self < base {
                return None;
            }

            // Since base >= self, n >= 1
            let mut n = 1;
            let mut r = base;

            // Optimization for 128+ bit wide integers.
            if Self::BITS >= $crate::UWide::BITS {
                // The following is a correct lower bound for ⌊log(base,self)⌋ because
                //
                // log(base,self) = log(2,self) / log(2,base)
                //                ≥ ⌊log(2,self)⌋ / (⌊log(2,base)⌋ + 1)
                //
                // hence
                //
                // ⌊log(base,self)⌋ ≥ ⌊ ⌊log(2,self)⌋ / (⌊log(2,base)⌋ + 1) ⌋ .
                n = self.ilog2() / (base.ilog2() + 1);
                r = base.pow(n);
            }

            while r <= self / base {
                n += 1;
                r *= base;
            }
            Some(n)
        }

        // FIXME: Stabilize when our MSRV goes to `1.67.0+`.
        // /// Returns the base 10 logarithm of the number, rounded down.
        // ///
        // /// Returns `None` if the number is zero.
        // #[inline(always)]
        // pub fn checked_ilog10(self) -> Option<u32> {
        //     match self.eq_const(Self::from_u8(0)) {
        //         true => None,
        //         false => {
        //             // NOTE: The `ilog10` implementations for small
        //             // numbers are quite efficient, so we use those
        //             // when available. We want to get this to
        //             // a 128-bit integer in as few multiplications
        //             // as we can.
        //             let mut log = 0;
        //             let mut value = self;
        //             const E16: u64 = 10_000_000_000_000_000;
        //             while value.high() > 0 {
        //                 value = value.div_wide(E16);
        //                 log += 16;
        //             }
        //             let value: u128 = value.as_u128();
        //             Some(value.ilog10() + log)
        //         },
        //     }
        // }

        /// Calculates the smallest value greater than or equal to `self` that
        /// is a multiple of `rhs`. Returns `None` if `rhs` is zero or the
        /// operation would result in overflow.
        #[doc = $crate::shared::docs::primitive_doc!($see_t, checked_next_multiple_of)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_next_multiple_of(self, rhs: Self) -> Option<Self> {
            match self.checked_rem(rhs) {
                None => None,
                Some(Self::MIN) => Some(self),
                // rhs - r cannot overflow because r is smaller than rhs
                Some(r) => self.checked_add(rhs.wrapping_sub(r)),
            }
        }

        /// Checked subtraction with a signed integer. Computes `self - rhs`,
        /// returning `None` if overflow occurred.
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_signed_diff(self, rhs: Self) -> Option<$s_t> {
            let res = self.wrapping_sub(rhs).as_signed();
            let overflow = self.ge_const(rhs) == res.lt_const(<$s_t>::from_u8(0));

            if !overflow {
                Some(res)
            } else {
                None
            }
        }

        /// Returns the smallest power of two greater than or equal to `self`. If
        /// the next power of two is greater than the type's maximum value,
        /// `None` is returned, otherwise the power of two is wrapped in `Some`.
        #[doc = $crate::shared::docs::primitive_doc!($see_t, checked_next_power_of_two)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_next_power_of_two(self) -> Option<Self> {
            self.one_less_than_next_power_of_two().checked_add(Self::from_u8(1))
        }
    };
}

pub(crate) use define;
