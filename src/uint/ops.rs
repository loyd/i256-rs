//! Defines high-level operations, which respect overflow checks.

#[rustfmt::skip]
macro_rules! define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        #[inline(always)]
        const fn is_div_overflow(self, rhs: Self) -> bool {
            _ = rhs;
            false
        }

        // If the checked methods should return `None`.
        #[inline(always)]
        const fn is_div_none(self, rhs: Self) -> bool {
            rhs.eq_const(Self::from_u8(0))
        }

        $crate::shared::ops::define!(type => $s_t, wide_type => $wide_t);

        /// Performs Euclidean division.
        ///
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this
        /// is exactly equal to `self / rhs`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::div_euclid`].")]
        #[inline(always)]
        pub fn div_euclid(self, rhs: Self) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_euclid(rhs)
            } else {
                match self.checked_div_euclid(rhs) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Calculates the least remainder of `self (mod rhs)`.
        ///
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this
        /// is exactly equal to `self % rhs`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::rem_euclid`].")]
        #[inline(always)]
        pub fn rem_euclid(self, rhs: Self) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_rem(rhs)
            } else {
                match self.checked_rem_euclid(rhs) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide by zero"),
                }
            }
        }

        /// Calculates the quotient of `self` and `rhs`, rounding the result towards
        /// negative infinity.
        ///
        /// This is the same as performing `self / rhs` for all unsigned integers.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::div_floor`].")]
        #[inline(always)]
        pub fn div_floor(self, rhs: Self) -> Self {
            self.wrapping_div(rhs)
        }

        /// Calculates the quotient of `self` and `rhs`, rounding the result towards
        /// positive infinity.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::div_ceil`].")]
        #[inline]
        pub fn div_ceil(self, rhs: Self) -> Self {
            let (d, r) = self.wrapping_div_rem(rhs);
            if !r.eq_const(Self::from_u8(0)) {
                // NOTE: This can't overflow
                d.wrapping_add_ulimb(1)
            } else {
                d
            }
        }

        /// Returns the logarithm of the number with respect to an arbitrary base,
        /// rounded down.
        ///
        /// This method might not be optimized owing to implementation details;
        /// `ilog2` can produce results more efficiently for base 2, and `ilog10`
        /// can produce results more efficiently for base 10.
        ///
        /// # Panics
        ///
        /// This function will panic if `self` is zero, or if `base` is less than 2.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::ilog`].")]
        #[inline(always)]
        pub fn ilog(self, base: Self) -> u32 {
            if let Some(log) = self.checked_ilog(base) {
                log
            } else {
                core::panic!("argument of integer logarithm must be positive")
            }
        }

        /// Returns the base 2 logarithm of the number, rounded down.
        ///
        /// # Panics
        ///
        /// This function will panic if `self` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::ilog2`].")]
        #[inline(always)]
        pub const fn ilog2(self) -> u32 {
            if let Some(log) = self.checked_ilog2() {
                log
            } else {
                core::panic!("argument of integer logarithm must be positive")
            }
        }

        // FIXME: Stabilize when our MSRV goes to `1.67.0+`.
        // /// Returns the base 10 logarithm of the number, rounded down.
        // ///
        // /// # Panics
        // ///
        // /// This function will panic if `self` is zero.
        // #[inline(always)]
        // pub fn ilog10(self) -> u32 {
        //     if let Some(log) = self.checked_ilog10() {
        //         log
        //     } else {
        //         core::panic!("argument of integer logarithm must be positive")
        //     }
        // }

        // FIXME: Stabilize when our MSRV goes to `1.84.0+`.
        // /// Returns the square root of the number, rounded down.
        // #[inline]
        // pub const fn isqrt(self) -> Self {
        //     todo!();
        // }

        /// Computes the absolute difference between `self` and `other`.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::abs_diff`].")]
        #[inline(always)]
        pub const fn abs_diff(self, other: Self) -> Self {
            if self.lt_const(other) {
                other.wrapping_sub(self)
            } else {
                self.wrapping_sub(other)
            }
        }

        /// Calculates the smallest value greater than or equal to `self` that
        /// is a multiple of `rhs`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        /// ## Overflow behavior
        ///
        /// On overflow, this function will panic if overflow checks are enabled
        /// (default in debug mode) and wrap if overflow checks are disabled
        /// (default in release mode).
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::next_multiple_of`].")]
        #[inline]
        pub fn next_multiple_of(self, rhs: Self) -> Self {
            match self.wrapping_rem(rhs) {
                Self::MIN => self,
                r => self.wrapping_add(rhs.wrapping_sub(r)),
            }
        }

        /// Returns `true` if `self` is an integer multiple of `rhs`, and false
        /// otherwise.
        ///
        /// This function is equivalent to `self % rhs == 0`, except that it will
        /// not panic for `rhs == 0`. Instead, `0.is_multiple_of(0) == true`,
        /// and for any non-zero `n`, `n.is_multiple_of(0) == false`.
        #[inline]
        pub fn is_multiple_of(self, rhs: Self) -> bool {
            match rhs {
                Self::MIN => self.eq_const(Self::MIN),
                _ => self.wrapping_rem(rhs).eq_const(Self::MIN),
            }
        }

        /// Returns `true` if and only if `self == 2^k` for some `k`.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::is_power_of_two`].")]
        #[inline(always)]
        pub const fn is_power_of_two(self) -> bool {
            self.count_ones() == 1
        }

        #[inline]
        const fn one_less_than_next_power_of_two(self) -> Self {
            if self.le_const(Self::from_u8(1)) {
                return Self::MIN;
            }
            let p = self.wrapping_sub(Self::from_u8(1));
            let z = p.leading_zeros();
            Self::MAX.wrapping_shr(z)
        }

        /// Returns the smallest power of two greater than or equal to `self`.
        ///
        /// When return value overflows (i.e., `self > (1 << (N-1))` for type
        /// `uN`), it panics in debug mode and the return value is wrapped to 0 in
        /// release mode (the only situation in which this method can return 0).
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::next_power_of_two`].")]
        #[inline]
        pub const fn next_power_of_two(self) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_next_power_of_two()
            } else {
                match self.checked_next_power_of_two() {
                    Some(v) => v,
                    None => core::panic!("attempt to add with overflow"),
                }
            }
        }

        /// Calculates the middle point of `self` and `rhs`.
        ///
        /// `midpoint(a, b)` is `(a + b) / 2` as if it were performed in a
        /// sufficiently-large unsigned integral type. This implies that the result
        /// is always rounded towards zero and that no overflow will ever occur.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::midpoint`].")]
        #[inline]
        #[must_use]
        pub const fn midpoint(self, rhs: Self) -> Self {
            // Use the well known branchless algorithm from Hacker's Delight to compute
            // `(a + b) / 2` without overflowing: `((a ^ b) >> 1) + (a & b)`.
            let xor = self.bitxor_const(rhs);
            xor.wrapping_shr(1).wrapping_add(self.bitand_const(rhs))
        }
    };
}

pub(crate) use define;
