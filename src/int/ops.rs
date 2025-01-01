//! Defines high-level operations, which respect overflow checks.

#[rustfmt::skip]
macro_rules! define {
    (
        unsigned_type => $u_t:ty,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        #[inline(always)]
        const fn is_div_overflow(self, rhs: Self) -> bool {
            self.eq_const(Self::MIN) & rhs.eq_const(Self::from_i8(-1))
        }

        // If the checked methods should return `None`.
        #[inline(always)]
        const fn is_div_none(self, rhs: Self) -> bool {
            rhs.eq_const(Self::from_u8(0)) || self.is_div_overflow(rhs)
        }

        /// Returns `true` if `self` is positive and `false` if the number is zero
        /// or negative.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, is_positive)]
        #[inline(always)]
        pub const fn is_positive(self) -> bool {
            // NOTE: This seems to optimize slightly better than the wide-based one.
            let high = self.most_significant_limb();
            if high < 0 {
                return false;
            } else if high > 0 {
                return true;
            }

            let mut i = Self::LIMBS - 1;
            while i > 0 {
                i -= 1;
                if self.get_limb(i) > 0 {
                    return true;
                }
            }
            false
        }

        /// Returns `true` if `self` is negative and `false` if the number is zero
        /// or positive.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, is_negative)]
        #[inline(always)]
        pub const fn is_negative(self) -> bool {
            // NOTE: Because this is 2's complement, we can optimize like this.
            let high = self.get_limb(Self::LIMBS - 1) as $crate::ILimb;
            high < 0
        }

        $crate::shared::ops::define!(
            type => $u_t,
            wide_type => $wide_t,
            see_type => $see_t,
        );

        /// Computes the absolute value of `self` without any wrapping
        /// or panicking.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, unsigned_abs)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn unsigned_abs(self) -> $u_t {
            self.wrapping_abs().as_unsigned()
        }

        /// Calculates the quotient of Euclidean division of `self` by `rhs`.
        ///
        /// This computes the integer `q` such that `self = q * rhs + r`, with
        /// `r = self.rem_euclid(rhs)` and `0 <= r < abs(rhs)`.
        ///
        /// In other words, the result is `self / rhs` rounded to the integer `q`
        /// such that `self >= q * rhs`.
        /// If `self > 0`, this is equal to rounding towards zero (the default in
        /// Rust); if `self < 0`, this is equal to rounding away from zero
        /// (towards +/- infinity). If `rhs > 0`, this is equal to rounding
        /// towards -infinity; if `rhs < 0`, this is equal to rounding towards
        /// +infinity.
        ///
        #[doc = $crate::shared::docs::div_by_zero_signed_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, div_euclid)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
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

        /// Calculates the least nonnegative remainder of `self (mod rhs)`.
        ///
        /// This is done as if by the Euclidean division algorithm -- given
        /// `r = self.rem_euclid(rhs)`, the result satisfies
        /// `self = rhs * self.div_euclid(rhs) + r` and `0 <= r < abs(rhs)`.
        ///
        #[doc = $crate::shared::docs::div_by_zero_signed_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, rem_euclid)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn rem_euclid(self, rhs: Self) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_rem_euclid(rhs)
            } else {
                match self.checked_rem_euclid(rhs) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Calculates the quotient of `self` and `rhs`, rounding the result towards
        /// negative infinity.
        ///
        #[doc = $crate::shared::docs::div_by_zero_signed_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, div_floor)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_floor(self, rhs: Self) -> Self {
            let (d, r) = self.wrapping_div_rem(rhs);

            // If the remainder is non-zero, we need to subtract one if the
            // signs of self and rhs differ, as this means we rounded upwards
            // instead of downwards. We do this branchlessly by creating a mask
            // which is all-ones iff the signs differ, and 0 otherwise. Then by
            // adding this mask (which corresponds to the signed value -1), we
            // get our correction.
            let correction = self.is_negative() ^ rhs.is_negative();
            if !r.eq_const(Self::from_u8(0)) {
                d.wrapping_sub_ulimb(correction as $crate::ULimb)
            } else {
                d
            }
        }

        /// Calculates the quotient of `self` and `rhs`, rounding the result towards
        /// positive infinity.
        ///
        #[doc = $crate::shared::docs::div_by_zero_signed_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, div_ceil)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_ceil(self, rhs: Self) -> Self {
            let (d, r) = self.wrapping_div_rem(rhs);

            // When remainder is non-zero we have a.div_ceil(b) == 1 + a.div_floor(b),
            // so we can re-use the algorithm from div_floor, just adding 1.
            let correction = Self::from_u8(1) + ((self ^ rhs) >> (Self::BITS - 1));
            if !r.eq_const(Self::from_u8(0)) {
                d.wrapping_add(correction)
            } else {
                d
            }
        }

        /// If `rhs` is positive, calculates the smallest value greater than or
        /// equal to `self` that is a multiple of `rhs`. If `rhs` is negative,
        /// calculates the largest value less than or equal to `self` that is a
        /// multiple of `rhs`.
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!()]
        ///
        #[doc = $crate::shared::docs::overflow_assertions_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, next_multiple_of)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn next_multiple_of(self, rhs: Self) -> Self {
            use core::ops::Rem;

            if rhs.eq_const(Self::from_i8(-1)) {
                return self;
            }

            let zero = Self::from_u8(0);
            let r = self.rem(rhs);
            let m = if (r > zero && rhs < zero) || (r < zero && rhs > zero) {
                r + rhs
            } else {
                r
            };

            if m.eq_const(zero) {
                self
            } else {
                self + (rhs - m)
            }
        }

        // FIXME: Stabilize when our MSRV goes to `1.84.0+`.
        // /// Returns the square root of the number, rounded down.
        // ///
        // /// # Panics
        // ///
        // /// This function will panic if `self` is negative.
        // #[inline]
        // pub const fn isqrt(self) -> Self {
        //     match self.checked_isqrt() {
        //         Some(sqrt) => sqrt,
        //         None => core::panic!("argument of integer square root cannot be
        // negative"),     }
        // }

        /// Returns the logarithm of the number with respect to an arbitrary base,
        /// rounded down.
        ///
        /// This method might not be optimized owing to implementation details;
        /// `ilog2` can produce results more efficiently for base 2, and `ilog10`
        /// can produce results more efficiently for base 10.
        ///
        /// # Panics
        ///
        /// This function will panic if `self` is less than or equal to zero,
        /// or if `base` is less than 2.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, ilog)]
        #[inline(always)]
        pub fn ilog(self, base: Self) -> u32 {
            assert!(
                base.ge_const(Self::from_u8(2)),
                "base of integer logarithm must be at least 2"
            );
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
        /// This function will panic if `self` is less than or equal to zero.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, ilog2)]
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
        // /// This function will panic if `self` is less than or equal to zero.
        // #[inline(always)]
        // pub fn ilog10(self) -> u32 {
        //     if let Some(log) = self.checked_ilog10() {
        //         log
        //     } else {
        //         core::panic!("argument of integer logarithm must be positive")
        //     }
        // }

        /// Computes the absolute value of `self`.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, abs)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn abs(self) -> Self {
            match self.checked_abs() {
                Some(value) => value,
                None => core::panic!("attempt to negate with overflow"),
            }
        }

        /// Computes the absolute difference between `self` and `other`.
        ///
        /// This function always returns the correct answer without overflow or
        /// panics by returning an unsigned integer.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, abs_diff)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn abs_diff(self, other: Self) -> $u_t {
            if self.lt_const(other) {
                other.as_unsigned().wrapping_sub(self.as_unsigned())
            } else {
                self.as_unsigned().wrapping_sub(other.as_unsigned())
            }
        }

        /// Returns a number representing sign of `self`.
        ///
        ///  - `0` if the number is zero
        ///  - `1` if the number is positive
        ///  - `-1` if the number is negative
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, signum)]
        #[inline(always)]
        pub const fn signum(self) -> Self {
            match self.cmp_const(Self::from_u8(0)) {
                core::cmp::Ordering::Less => Self::from_i8(-1),
                core::cmp::Ordering::Equal => Self::from_u8(0),
                core::cmp::Ordering::Greater => Self::from_u8(1),
            }
        }

        /// Calculates the middle point of `self` and `rhs`.
        ///
        /// `midpoint(a, b)` is `(a + b) / 2` as if it were performed in a
        /// sufficiently-large unsigned integral type. This implies that the
        /// result is always rounded towards negative infinity and that no
        /// overflow will ever occur.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, midpoint)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn midpoint(self, rhs: Self) -> Self {
            // Use the well known branchless algorithm from Hacker's Delight to compute
            // `(a + b) / 2` without overflowing: `((a ^ b) >> 1) + (a & b)`.
            let xor = self.bitxor_const(rhs);
            let t = xor.wrapping_shr(1).wrapping_add(self.bitand_const(rhs));
            // Except that it fails for integers whose sum is an odd negative number as
            // their floor is one less than their average. So we adjust the result.
            let is_negative = Self::from_u8(t.is_negative() as u8);
            t.wrapping_add(is_negative.bitand_const(xor))
        }
    };
}

pub(crate) use define;
