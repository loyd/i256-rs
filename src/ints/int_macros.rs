//! Macros for signed, fixed width big integers.
//!
//! A lot of these depend on methods from other defines, so if
//! implementing your own produces many errors, look through
//! and custom implement the types required.

#[rustfmt::skip]
macro_rules! int_associated_consts_define {
    (
        bits => $bits:expr,
        max_digits => $max_digits:expr,
        wide_type => $wide_t:ty $(,)?
    ) => {
        associated_consts_define!(
            bits => $bits,
            max_digits => $max_digits,
            wide_type => $wide_t,
            low_type => $crate::ULimb,
            high_type => $crate::ILimb,
        );

        #[doc = concat!("New code should prefer to use  [`", stringify!($wide_t), "::MIN`] instead.")]
        ///
        /// Returns the smallest value that can be represented by this integer type.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::min_value`].")]
        #[inline(always)]
        #[deprecated]
        pub const fn min_value() -> Self {
            let mut limbs = [0; Self::LIMBS];
            ne_index!(limbs[Self::LIMBS - 1] = $crate::ILimb::MIN as $crate::ULimb);
            Self::from_ne_limbs(limbs)
        }

        #[doc = concat!("New code should prefer to use  [`", stringify!($wide_t), "::MAX`] instead.")]
        ///
        /// Returns the largest value that can be represented by this integer type.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::max_value`].")]
        #[inline(always)]
        #[deprecated]
        pub const fn max_value() -> Self {
            let mut limbs = [$crate::ULimb::MAX; Self::LIMBS];
            ne_index!(limbs[Self::LIMBS - 1] = $crate::ILimb::MAX as $crate::ULimb);
            Self::from_ne_limbs(limbs)
        }
    };
}

macro_rules! int_cmp_define {
    (
        low_type => $lo_t:ty,
        high_type => $hi_t:ty,
        short_circuit => $short_circuit:tt $(,)?
    ) => {
        cmp_define!(
            low_type => $lo_t,
            high_type => $hi_t,
            short_circuit => $short_circuit,
        );
    };
}

macro_rules! int_bitops_define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        bitops_define!(type => $u_t, wide_type => $wide_t);

        /// Shifts the bits to the left by a specified amount, `n`,
        /// wrapping the truncated bits to the end of the resulting integer.
        ///
        /// Please note this isn't the same operation as the `<<` shifting operator!
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::rotate_left`].")]
        #[inline(always)]
        pub const fn rotate_left(self, n: u32) -> Self {
            self.as_unsigned().rotate_left(n).as_signed()
        }

        /// Shifts the bits to the right by a specified amount, `n`,
        /// wrapping the truncated bits to the beginning of the resulting
        /// integer.
        ///
        /// Please note this isn't the same operation as the `>>` shifting operator!
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::rotate_right`].")]
        #[inline(always)]
        pub const fn rotate_right(self, n: u32) -> Self {
            self.as_unsigned().rotate_right(n).as_signed()
        }

        /// Panic-free bitwise shift-left; yields `self << mask(rhs)`, where `mask`
        /// removes any high-order bits of `rhs` that would cause the shift to
        /// exceed the bitwidth of the type.
        ///
        /// Note that this is *not* the same as a rotate-left; the RHS of a wrapping
        /// shift-left is restricted to the range of the type, rather than the
        /// bits shifted out of the LHS being returned to the other end.
        /// The primitive integer types all implement a
        /// [`rotate_left`](Self::rotate_left) function, which may be what you
        /// want instead.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_shl`].")]
        #[inline(always)]
        pub const fn wrapping_shl(self, rhs: u32) -> Self {
            #[cfg(not(feature = "limb32"))]
            let result = math::shl_i128(self.to_ne_wide(), rhs % Self::BITS);

            #[cfg(feature = "limb32")]
            let result = math::shl_i64(self.to_ne_wide(), rhs % Self::BITS);

            Self::from_ne_wide(result)
        }

        /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`, where `mask`
        /// removes any high-order bits of `rhs` that would cause the shift to
        /// exceed the bitwidth of the type.
        ///
        /// Note that this is *not* the same as a rotate-right; the RHS of a
        /// wrapping shift-right is restricted to the range of the type, rather
        /// than the bits shifted out of the LHS being returned to the other
        /// end. The primitive integer types all implement a
        /// [`rotate_right`](Self::rotate_right) function, which may be what you
        /// want instead.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_shr`].")]
        #[inline(always)]
        pub const fn wrapping_shr(self, rhs: u32) -> Self {
            #[cfg(not(feature = "limb32"))]
            let result = math::shr_i128(self.to_ne_wide(), rhs % Self::BITS);

            #[cfg(feature = "limb32")]
            let result = math::shr_i64(self.to_ne_wide(), rhs % Self::BITS);

            Self::from_ne_wide(result)
        }
    };
}

macro_rules! int_byte_order_define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        byte_order_define!(type => $u_t, wide_type => $wide_t);
    };
}

#[rustfmt::skip]
macro_rules! int_casts_define {
    (
        unsigned_type => $u_t:ty,
        bits => $bits:expr,
        wide_type => $wide_t:ty,
        kind => $kind:ident $(,)?
    ) => {
        casts_define!(
            bits => $bits,
            kind => $kind,
        );

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from an unsigned integer, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_unsigned(value: $u_t) -> Self {
            Self::from_ne_limbs(value.to_ne_limbs())
        }

        #[doc = concat!("Create the ", stringify!($bits), "-bit ", stringify!($kind), " integer from a signed integer, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn from_signed(value: Self) -> Self {
            value
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " unsigned integer to the unsigned type, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_unsigned(&self) -> $u_t {
            <$u_t>::from_ne_limbs(self.to_ne_limbs())
        }

        #[doc = concat!("Convert the ", stringify!($bits), "-bit ", stringify!($kind), " unsigned integer to the signed type, as if by an `as` cast.")]
        #[inline(always)]
        pub const fn as_signed(&self) -> Self {
            *self
        }

        /// Returns the bit pattern of `self` reinterpreted as an unsigned integer
        /// of the same size.
        ///
        /// This produces the same result as an `as` cast, but ensures that the
        /// bit-width remains the same.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::cast_unsigned`].")]
        #[inline(always)]
        pub const fn cast_unsigned(self) -> $u_t {
            self.as_unsigned()
        }
    };
}

macro_rules! int_extensions_define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        extensions_define!(type => $u_t, wide_type => $wide_t);

        /// Get the most significant limb in the buiffer.
        #[inline(always)]
        pub const fn most_significant_limb(&self) -> $crate::ILimb {
            self.get_limb(Self::LIMBS - 1) as $crate::ILimb
        }
    };
}

#[rustfmt::skip]
macro_rules! int_ops_define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
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
        #[doc = concat!("See [`", stringify!($wide_t), "::is_positive`].")]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::is_negative`].")]
        #[inline(always)]
        pub const fn is_negative(self) -> bool {
            // NOTE: Because this is 2's complement, we can optimize like this.
            let high = self.get_limb(Self::LIMBS - 1) as $crate::ILimb;
            high < 0
        }

        ops_define!(type => $u_t, wide_type => $wide_t);

        /// Computes the absolute value of `self` without any wrapping
        /// or panicking.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::unsigned_abs`].")]
        #[inline(always)]
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
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero or if `self` is `Self::MIN`
        /// and `rhs` is -1. This behavior is not affected by the `overflow-checks`
        /// flag.
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

        /// Calculates the least nonnegative remainder of `self (mod rhs)`.
        ///
        /// This is done as if by the Euclidean division algorithm -- given
        /// `r = self.rem_euclid(rhs)`, the result satisfies
        /// `self = rhs * self.div_euclid(rhs) + r` and `0 <= r < abs(rhs)`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero or if `self` is `Self::MIN`
        /// and `rhs` is -1. This behavior is not affected by the
        /// `overflow-checks` flag.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::rem_euclid`].")]
        #[inline(always)]
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
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero or if `self` is `Self::MIN`
        /// and `rhs` is -1. This behavior is not affected by the `overflow-checks`
        /// flag.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::div_floor`].")]
        #[inline]
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
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero or if `self` is `Self::MIN`
        /// and `rhs` is -1. This behavior is not affected by the `overflow-checks`
        /// flag.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::div_ceil`].")]
        #[inline]
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
            if rhs.eq_const(Self::from_i8(-1)) {
                return self;
            }

            let zero = Self::from_u8(0);
            let r = self.wrapping_rem(rhs);
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
        #[doc = concat!("See [`", stringify!($wide_t), "::ilog`].")]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::abs`].")]
        #[inline(always)]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::abs_diff`].")]
        #[inline(always)]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::signum`].")]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::midpoint`].")]
        #[inline]
        #[must_use]
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

macro_rules! int_bigint_define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        bigint_define!(type => $u_t, wide_type => $wide_t);
    };
}

#[rustfmt::skip]
macro_rules! int_wrapping_define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        wrapping_define!(type => $u_t, wide_type => $wide_t);

        /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at
        /// the boundary of the type.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_add`].")]
        #[inline(always)]
        pub const fn wrapping_add(self, rhs: Self) -> Self {
            let lhs = self.to_ne_limbs();
            let rhs = rhs.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let result = math::wrapping_add_i64(&lhs, &rhs);

            #[cfg(feature = "limb32")]
            let result = math::wrapping_add_i32(&lhs, &rhs);

            Self::from_ne_limbs(result)
        }

        /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around
        /// at the boundary of the type.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_sub`].")]
        #[inline(always)]
        pub const fn wrapping_sub(self, rhs: Self) -> Self {
            let lhs = self.to_ne_limbs();
            let rhs = rhs.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let result = math::wrapping_sub_i64(&lhs, &rhs);

            #[cfg(feature = "limb32")]
            let result = math::wrapping_sub_i32(&lhs, &rhs);

            Self::from_ne_limbs(result)
        }

        /// Wrapping (modular) subtraction with an unsigned integer. Computes
        /// `self - rhs`, wrapping around at the boundary of the type.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_sub_unsigned`].")]
        #[inline(always)]
        pub const fn wrapping_sub_unsigned(self, rhs: $u_t) -> Self {
            self.wrapping_sub(Self::from_unsigned(rhs))
        }

        /// Wrapping (modular) multiplication. Computes `self * rhs`, wrapping
        /// around at the boundary of the type.
        ///
        /// This in worst case 10 `mul` and 13 `add` instructions, because of
        /// branching in nearly every case, it has better performance and
        /// optimizes nicely for small multiplications. See [`u256::wrapping_mul`]
        /// for a more detailed analysis, which is identical.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_mul`].")]
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline(always)]
        pub const fn wrapping_mul(self, rhs: Self) -> Self {
            let lhs = self.to_ne_limbs();
            let rhs = rhs.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let limbs = math::wrapping_mul_i64(&lhs, &rhs);

            #[cfg(feature = "limb32")]
            let limbs = math::wrapping_mul_i32(&lhs, &rhs);

            Self::from_ne_limbs(limbs)
        }

        /// Div/Rem operation on the integer.
        ///
        /// This allows storing of both the quotient and remainder without
        /// making repeated calls.
        ///
        /// # Panics
        ///
        /// This panics if the divisor is 0.
        #[inline]
        pub fn wrapping_div_rem(self, n: Self) -> (Self, Self) {
            // NOTE: Our algorithm assumes little-endian order, which we might not have.
            // So, we transmute to LE order prior to the call.
            // Do division as positive numbers, and if `lhs.is_sign_negative() ^
            // rhs.is_sign_negative()`, then we can inver the sign
            let x = self.unsigned_abs().to_le_limbs();
            let y = n.unsigned_abs().to_le_limbs();

            // get our unsigned division product
            let (div, rem) = math::div_rem_full(&x, &y);
            let mut div = u256::from_le_limbs(div).as_signed();
            let mut rem = u256::from_le_limbs(rem).as_signed();

            // convert to our correct signs, get the product
            // NOTE: Rust has different behavior than languages like
            // Python, where `-1 % 2 == 1` and `-1 % -2 == -1`. In
            // Rust, both are `-1`.
            if self.is_negative() != n.is_negative() {
                div = div.wrapping_neg();
            }
            if self.is_negative() {
                rem = rem.wrapping_neg();
            }

            (div, rem)
        }

        /// Wrapping (modular) division. Computes `self / rhs`, wrapping around at
        /// the boundary of the type.
        ///
        /// The only case where such wrapping can occur is when one divides `MIN /
        /// -1` on a signed type (where `MIN` is the negative minimal value for
        /// the type); this is equivalent to `-MIN`, a positive value
        /// that is too large to represent in the type. In such a case, this
        /// function returns `MIN` itself.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_div`].")]
        #[inline(always)]
        pub fn wrapping_div(self, rhs: Self) -> Self {
            self.wrapping_div_rem(rhs).0
        }

        /// Wrapping Euclidean division. Computes `self.div_euclid(rhs)`,
        /// wrapping around at the boundary of the type.
        ///
        /// Wrapping will only occur in `MIN / -1` on a signed type (where `MIN` is
        /// the negative minimal value for the type). This is equivalent to
        /// `-MIN`, a positive value that is too large to represent in the type.
        /// In this case, this method returns `MIN` itself.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_div_euclid`].")]
        #[inline]
        pub fn wrapping_div_euclid(self, rhs: Self) -> Self {
            let (mut q, r) = self.wrapping_div_rem(rhs);
            if r.is_negative() {
                if rhs.is_positive() {
                    q = q.wrapping_sub_ulimb(1);
                } else {
                    q = q.wrapping_add_ulimb(1);
                }
            }
            q
        }

        /// Wrapping (modular) remainder. Computes `self % rhs`, wrapping around at
        /// the boundary of the type.
        ///
        /// Such wrap-around never actually occurs mathematically; implementation
        /// artifacts make `x % y` invalid for `MIN / -1` on a signed type
        /// (where `MIN` is the negative minimal value). In such a case,
        /// this function returns `0`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_rem`].")]
        #[inline(always)]
        pub fn wrapping_rem(self, rhs: Self) -> Self {
            self.wrapping_div_rem(rhs).1
        }

        /// Wrapping Euclidean remainder. Computes `self.rem_euclid(rhs)`, wrapping
        /// around at the boundary of the type.
        ///
        /// Wrapping will only occur in `MIN % -1` on a signed type (where `MIN` is
        /// the negative minimal value for the type). In this case, this method
        /// returns 0.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_rem_euclid`].")]
        #[inline]
        pub fn wrapping_rem_euclid(self, rhs: Self) -> Self {
            let r = self.wrapping_rem(rhs);
            if r.is_negative() {
                // Semantically equivalent to `if rhs < 0 { r - rhs } else { r + rhs }`.
                // If `rhs` is not `Self::MIN`, then `r + abs(rhs)` will not overflow
                // and is clearly equivalent, because `r` is negative.
                // Otherwise, `rhs` is `Self::MIN`, then we have
                // `r.wrapping_add(Self::MIN.wrapping_abs())`, which evaluates
                // to `r.wrapping_add(Self::MIN)`, which is equivalent to
                // `r - Self::MIN`, which is what we wanted (and will not overflow
                // for negative `r`).
                r.wrapping_add(rhs.wrapping_abs())
            } else {
                r
            }
        }

        /// Wrapping (modular) negation. Computes `-self`, wrapping around at the
        /// boundary of the type.
        ///
        /// The only case where such wrapping can occur is when one negates `MIN` on
        /// a signed type (where `MIN` is the negative minimal value for the
        /// type); this is a positive value that is too large to represent
        /// in the type. In such a case, this function returns `MIN` itself.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_neg`].")]
        #[inline(always)]
        pub const fn wrapping_neg(self) -> Self {
            // NOTE: This is identical to `add(not(x), 1i256)`
            let twos_neg = self.not_const().wrapping_add_ulimb(1);
            let from_zero = Self::from_u8(0).wrapping_sub(self);
            debug_assert!(from_zero.eq_const(twos_neg));
            from_zero
        }

        /// Wrapping (modular) absolute value. Computes `self.abs()`, wrapping
        /// around at the boundary of the type.
        ///
        /// The only case where such wrapping can occur is when one takes the
        /// absolute value of the negative minimal value for the type; this is a
        /// positive value that is too large to represent in the type. In such a
        /// case, this function returns `MIN` itself.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_abs`].")]
        #[inline(always)]
        pub const fn wrapping_abs(self) -> Self {
            self.overflowing_abs().0
        }
    };
}

#[rustfmt::skip]
macro_rules! int_overflowing_define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        overflowing_define!(type => $u_t, wide_type => $wide_t);

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

            #[cfg(not(feature = "limb32"))]
            let (limbs, overflowed) = math::overflowing_add_i64(&lhs, &rhs);

            #[cfg(feature = "limb32")]
            let (limbs, overflowed) = math::overflowing_add_i32(&lhs, &rhs);

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

            #[cfg(not(feature = "limb32"))]
            let (limbs, overflowed) = math::overflowing_sub_i64(&lhs, &rhs);

            #[cfg(feature = "limb32")]
            let (limbs, overflowed) = math::overflowing_sub_i32(&lhs, &rhs);

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

            #[cfg(not(feature = "limb32"))]
            let (limbs, overflowed) = math::overflowing_mul_i64(&lhs, &rhs);

            #[cfg(feature = "limb32")]
            let (limbs, overflowed) = math::overflowing_mul_i32(&lhs, &rhs);

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

#[rustfmt::skip]
macro_rules! int_saturating_define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        saturating_define!(type => $u_t, wide_type => $wide_t);

        /// Saturating integer addition. Computes `self + rhs`, saturating at the
        /// numeric bounds instead of overflowing.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_add`].")]
        #[inline(always)]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_add_unsigned`].")]
        #[inline(always)]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_sub`].")]
        #[inline(always)]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_sub_unsigned`].")]
        #[inline(always)]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_neg`].")]
        #[inline(always)]
        pub const fn saturating_neg(self) -> Self {
            Self::from_u8(0).saturating_sub(self)
        }

        /// Saturating absolute value. Computes `self.abs()`, returning `MAX` if
        /// `self == MIN` instead of overflowing.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_abs`].")]
        #[inline(always)]
        pub const fn saturating_abs(self) -> Self {
            match self.checked_abs() {
                Some(value) => value,
                None => Self::MAX,
            }
        }

        /// Saturating integer multiplication. Computes `self * rhs`, saturating at
        /// the numeric bounds instead of overflowing.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_mul`].")]
        #[inline]
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
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_div`].")]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_pow`].")]
        #[inline]
        pub const fn saturating_pow(self, exp: u32) -> Self {
            match self.checked_pow(exp) {
                Some(x) => x,
                None if self.lt_const(Self::from_u8(0)) && exp % 2 == 1 => Self::MIN,
                None => Self::MAX,
            }
        }
    };
}

#[rustfmt::skip]
macro_rules! int_checked_define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        checked_define!(type => $u_t, wide_type => $wide_t);

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

#[rustfmt::skip]
macro_rules! int_strict_define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        strict_define!(type => $u_t, wide_type => $wide_t);

        /// Strict addition with an unsigned integer. Computes `self + rhs`,
        /// panicking if overflow occurred.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_add_unsigned`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub const fn strict_add_unsigned(self, rhs: $u_t) -> Self {
            match self.checked_add_unsigned(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to add with overflow"),
            }
        }

        /// Strict subtraction with an unsigned integer. Computes `self - rhs`,
        /// panicking if overflow occurred.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_sub_unsigned`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub const fn strict_sub_unsigned(self, rhs: $u_t) -> Self {
            match self.checked_sub_unsigned(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to subtract with overflow"),
            }
        }

        /// Strict integer division. Computes `self / rhs`, panicking
        /// if overflow occurred.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        /// The only case where such an overflow can occur is when one divides `MIN
        /// / -1` on a signed type (where `MIN` is the negative minimal value
        /// for the type.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_div`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub fn strict_div(self, rhs: Self) -> Self {
            match self.checked_div(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to divide with overflow"),
            }
        }

        /// Strict integer remainder. Computes `self % rhs`, panicking if
        /// the division results in overflow.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        /// The only case where such an overflow can occur is `x % y` for `MIN / -1`
        /// on a signed type (where `MIN` is the negative minimal value), which
        /// is invalid due to implementation artifacts.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_rem`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub fn strict_rem(self, rhs: Self) -> Self {
            match self.checked_rem(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to divide with overflow"),
            }
        }

        /// Strict Euclidean division. Computes `self.div_euclid(rhs)`, panicking
        /// if overflow occurred.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        /// The only case where such an overflow can occur is when one divides `MIN
        /// / -1` on a signed type (where `MIN` is the negative minimal value
        /// for the type); this is equivalent to `-MIN`, a positive value
        /// that is too large to represent in the type.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_div_euclid`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub fn strict_div_euclid(self, rhs: Self) -> Self {
            match self.checked_div_euclid(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to divide with overflow"),
            }
        }

        /// Strict Euclidean remainder. Computes `self.rem_euclid(rhs)`, panicking
        /// if the division results in overflow.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        /// The only case where such an overflow can occur is `x % y` for `MIN / -1`
        /// on a signed type (where `MIN` is the negative minimal value), which
        /// is invalid due to implementation artifacts.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_rem_euclid`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub fn strict_rem_euclid(self, rhs: Self) -> Self {
            match self.checked_rem_euclid(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to divide with overflow"),
            }
        }

        /// Strict negation. Computes `-self`, panicking if `self == MIN`.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_neg`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub const fn strict_neg(self) -> Self {
            match self.checked_neg() {
                Some(v) => v,
                None => core::panic!("attempt to negate with overflow"),
            }
        }

        /// Strict absolute value. Computes `self.abs()`, panicking if
        /// `self == MIN`.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_abs`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub const fn strict_abs(self) -> Self {
            match self.checked_abs() {
                Some(v) => v,
                None => core::panic!("attempt to negate with overflow"),
            }
        }

        /// Unchecked negation. Computes `-self`, assuming overflow cannot occur.
        ///
        /// # Safety
        ///
        /// This results in undefined behavior when the value overflows.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::unchecked_neg`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[must_use]
        #[inline(always)]
        pub unsafe fn unchecked_neg(self) -> Self {
            match self.checked_neg() {
                Some(value) => value,
                // SAFETY: this is guaranteed to be safe by the caller.
                None => unsafe { core::hint::unreachable_unchecked() },
            }
        }
    };
}

macro_rules! int_unchecked_define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        unchecked_define!(type => $u_t, wide_type => $wide_t);
    };
}

macro_rules! int_unbounded_define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        unbounded_define!(type => $u_t, wide_type => $wide_t);
    };
}

macro_rules! int_limb_ops_define {
    () => {
        limb_ops_define!();

        /// Add a signed limb to the big integer.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn add_ilimb(self, n: $crate::ILimb) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_add_ilimb(n)
            } else {
                match self.checked_add_ilimb(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to add with overflow"),
                }
            }
        }

        /// Subtract a signed limb from the big integer.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn sub_ilimb(self, n: $crate::ILimb) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_sub_ilimb(n)
            } else {
                match self.checked_sub_ilimb(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to subtract with overflow"),
                }
            }
        }

        /// Multiply our big integer by a signed limb.
        ///
        /// This allows optimizations a full multiplication cannot do.
        #[inline(always)]
        pub const fn mul_ilimb(self, n: $crate::ILimb) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_mul_ilimb(n)
            } else {
                match self.checked_mul_ilimb(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to multiply with overflow"),
                }
            }
        }

        /// Get the quotient and remainder of our big integer divided
        /// by a signed limb.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline]
        pub fn div_rem_ilimb(self, n: $crate::ILimb) -> (Self, $crate::ILimb) {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_rem_ilimb(n)
            } else {
                match self.checked_div_rem_ilimb(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Get the quotient of our big integer divided by a signed limb.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn div_ilimb(self, n: $crate::ILimb) -> Self {
            self.div_rem_ilimb(n).0
        }

        /// Get the remainder of our big integer divided by a signed limb.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn rem_ilimb(self, n: $crate::ILimb) -> $crate::ILimb {
            self.div_rem_ilimb(n).1
        }
    };

    (@wrapping) => {
        limb_ops_define!(@wrapping);

        /// Add an unsigned limb to the big integer, wrapping on overflow.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn wrapping_add_ulimb(self, n: ULimb) -> Self {
            let lhs = self.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let limbs = math::wrapping_add_ulimb_i64(&lhs, n);

            #[cfg(feature = "limb32")]
            let limbs = math::wrapping_add_ulimb_i32(&lhs, n);

            Self::from_ne_limbs(limbs)
        }

        /// Add a signed limb to the big integer, wrapping on overflow.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn wrapping_add_ilimb(self, n: ILimb) -> Self {
            let lhs = self.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let limbs = math::wrapping_add_ilimb_i64(&lhs, n);

            #[cfg(feature = "limb32")]
            let limbs = math::wrapping_add_ilimb_i32(&lhs, n);

            Self::from_ne_limbs(limbs)
        }

        /// Subtract an unsigned limb from the big integer, wrapping on
        /// overflow.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn wrapping_sub_ulimb(self, n: ULimb) -> Self {
            let lhs = self.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let limbs = math::wrapping_sub_ulimb_i64(&lhs, n);

            #[cfg(feature = "limb32")]
            let limbs = math::wrapping_sub_ulimb_i32(&lhs, n);

            Self::from_ne_limbs(limbs)
        }

        /// Subtract a signed limb from the big integer, wrapping on
        /// overflow.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn wrapping_sub_ilimb(self, n: ILimb) -> Self {
            let lhs = self.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let limbs = math::wrapping_sub_ilimb_i64(&lhs, n);

            #[cfg(feature = "limb32")]
            let limbs = math::wrapping_sub_ilimb_i32(&lhs, n);

            Self::from_ne_limbs(limbs)
        }

        /// Multiply our big integer by an unsigned limb, wrapping on overflow.
        ///
        /// This allows optimizations a full multiplication cannot do.
        /// This in worst case 5 `mul`, 3 `add`, and 6 `sub` instructions,
        /// because of branching in nearly every case, it has better
        /// performance and optimizes nicely for small multiplications.
        /// See [`u256::wrapping_mul_ulimb`] for a more detailed analysis,
        /// which is identical.
        #[inline(always)]
        pub const fn wrapping_mul_ulimb(self, n: ULimb) -> Self {
            let lhs = self.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let limbs = math::wrapping_mul_ulimb_i64(&lhs, n);

            #[cfg(feature = "limb32")]
            let limbs = math::wrapping_mul_ulimb_i32(&lhs, n);

            Self::from_ne_limbs(limbs)
        }

        /// Multiply our big integer by a signed limb, wrapping on overflow.
        ///
        /// This allows optimizations a full multiplication cannot do.
        /// This in worst case 4 `mul`, 3 `add`, and 6 `sub` instructions,
        /// because of branching in nearly every case, it has better
        /// performance and optimizes nicely for small multiplications.
        #[inline(always)]
        pub const fn wrapping_mul_ilimb(self, n: ILimb) -> Self {
            let lhs = self.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let limbs = math::wrapping_mul_ilimb_i64(&lhs, n);

            #[cfg(feature = "limb32")]
            let limbs = math::wrapping_mul_ilimb_i32(&lhs, n);

            Self::from_ne_limbs(limbs)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by an unsigned limb, wrapping on overflow.
        ///
        /// This allows optimizations a full division cannot do. This always
        /// wraps, which can never happen in practice. This has to use
        /// the floor division since we can never have a non-negative rem.
        #[inline]
        pub fn wrapping_div_rem_ulimb(self, n: ULimb) -> (Self, ULimb) {
            let x = self.unsigned_abs().to_le_limbs();
            let (div, mut rem) = math::div_rem_limb(&x, n);
            let mut div = Self::from_le_limbs(div);
            if self.is_negative() {
                div = div.wrapping_neg();
            }
            // rem is always positive: `-65 % 64` is 63
            // however, if we're negative and have a remainder,
            // we need to adjust since the remainder assumes the
            // floor of a positive value
            if self.is_negative() && rem != 0 {
                div -= Self::from_u8(1);
                rem = n - rem;
            }
            (div, rem)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by a signed limb, wrapping on overflow.
        ///
        /// This allows optimizations a full division cannot do. This always
        /// wraps, which can never happen in practice.
        #[inline]
        pub fn wrapping_div_rem_ilimb(self, n: ILimb) -> (Self, ILimb) {
            let x = self.unsigned_abs().to_le_limbs();
            let (div, rem) = math::div_rem_limb(&x, n.unsigned_abs());
            let mut div = Self::from_le_limbs(div);
            let mut rem = rem as ILimb;

            // convert to our correct signs, get the product
            // NOTE: Rust has different behavior than languages like
            // Python, where `-1 % 2 == 1` and `-1 % -2 == -1`. In
            // Rust, both are `-1`.
            if self.is_negative() != n.is_negative() {
                div = div.wrapping_neg();
            }
            if self.is_negative() {
                rem = rem.wrapping_neg();
            }

            (div, rem)
        }

        /// Get the quotient of our big integer divided
        /// by a signed limb, wrapping on overflow.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn wrapping_div_ilimb(self, n: $crate::ILimb) -> Self {
            self.wrapping_div_rem_ilimb(n).0
        }

        /// Get the remainder of our big integer divided
        /// by a signed limb, wrapping on overflow.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn wrapping_rem_ilimb(self, n: $crate::ILimb) -> $crate::ILimb {
            self.wrapping_div_rem_ilimb(n).1
        }
    };

    (@overflowing) => {
        limb_ops_define!(@overflowing);

        /// Add an unsigned limb to the big integer, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn overflowing_add_ulimb(self, n: ULimb) -> (Self, bool) {
            let lhs = self.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let (limbs, overflowed) = math::overflowing_add_ulimb_i64(&lhs, n);

            #[cfg(feature = "limb32")]
            let (limbs, overflowed) = math::overflowing_add_ulimb_i32(&lhs, n);

            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Add a signed limb to the big integer, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn overflowing_add_ilimb(self, n: ILimb) -> (Self, bool) {
            let lhs = self.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let (limbs, overflowed) = math::overflowing_add_ilimb_i64(&lhs, n);

            #[cfg(feature = "limb32")]
            let (limbs, overflowed) = math::overflowing_add_ilimb_i32(&lhs, n);

            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Subtract an unsigned limb from the big integer, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn overflowing_sub_ulimb(self, n: ULimb) -> (Self, bool) {
            let lhs = self.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let (limbs, overflowed) = math::overflowing_sub_ulimb_i64(&lhs, n);

            #[cfg(feature = "limb32")]
            let (limbs, overflowed) = math::overflowing_sub_ulimb_i32(&lhs, n);

            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Subtract a signed limb from the big integer, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn overflowing_sub_ilimb(self, n: ILimb) -> (Self, bool) {
            let lhs = self.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let (limbs, overflowed) = math::overflowing_sub_ilimb_i64(&lhs, n);

            #[cfg(feature = "limb32")]
            let (limbs, overflowed) = math::overflowing_sub_ilimb_i32(&lhs, n);

            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Multiply our big integer by an unsigned limb, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full multiplication cannot do.
        /// This in worst case 4 `mul`, 4 `add`, and 6 `sub` instructions,
        /// significantly slower than the wrapping variant.
        #[inline(always)]
        pub const fn overflowing_mul_ulimb(self, n: ULimb) -> (Self, bool) {
            let lhs = self.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let (limbs, overflowed) = math::overflowing_mul_ulimb_i64(&lhs, n);

            #[cfg(feature = "limb32")]
            let (limbs, overflowed) = math::overflowing_mul_ulimb_i32(&lhs, n);

            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Multiply our big integer by a signed limb, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full multiplication cannot do.
        /// This in worst case 5 `mul`, 5 `add`, and 6 `sub` instructions,
        /// significantly slower than the wrapping variant.
        #[inline(always)]
        pub const fn overflowing_mul_ilimb(self, n: ILimb) -> (Self, bool) {
            let lhs = self.to_ne_limbs();

             #[cfg(not(feature = "limb32"))]
            let (limbs, overflowed) = math::overflowing_mul_ilimb_i64(&lhs, n);

            #[cfg(feature = "limb32")]
            let (limbs, overflowed) = math::overflowing_mul_ilimb_i32(&lhs, n);

            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by a signed limb, returning the value and if overflow
        /// occurred.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline]
        pub fn overflowing_div_rem_ilimb(self, n: $crate::ILimb) -> ((Self, $crate::ILimb), bool) {
            if self.eq_const(Self::MIN) && n == -1 {
                ((Self::MIN, 0), true)
            } else {
                (self.wrapping_div_rem_ilimb(n), false)
            }
        }

        /// Get the quotient of our big integer divided
        /// by a signed limb, returning the value and if overflow
        /// occurred.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn overflowing_div_ilimb(self, n: $crate::ILimb) -> (Self, bool) {
            let (value, overflowed) = self.overflowing_div_rem_ilimb(n);
            (value.0, overflowed)
        }

        /// Get the remainder of our big integer divided
        /// by a signed limb, returning the value and if overflow
        /// occurred.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn overflowing_rem_ilimb(self, n: $crate::ILimb) -> ($crate::ILimb, bool) {
            let (value, overflowed) = self.overflowing_div_rem_ilimb(n);
            (value.1, overflowed)
        }
    };

    (@checked) => {
        limb_ops_define!(@checked);

        /// Add a signed limb to the big integer, returning None on overflow.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn checked_add_ilimb(self, n: $crate::ILimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add_ilimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Subtract a signed limb from the big integer, returning None on overflow.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn checked_sub_ilimb(self, n: $crate::ILimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_sub_ilimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Multiply our big integer by a signed limb, returning None on overflow.
        ///
        /// This allows optimizations a full multiplication cannot do.
        #[inline(always)]
        pub const fn checked_mul_ilimb(self, n: $crate::ILimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_mul_ilimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Get the quotient and remainder of our big integer divided
        /// by a signed limb, returning None on overflow or division by 0.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline]
        pub fn checked_div_rem_ilimb(self, n: $crate::ILimb) -> Option<(Self, $crate::ILimb)> {
            if n == 0 {
                None
            } else {
                Some(self.wrapping_div_rem_ilimb(n))
            }
        }

        /// Get the quotient of our big integer divided by a signed
        /// limb, returning None on overflow or division by 0.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn checked_div_ilimb(self, n: $crate::ILimb) -> Option<Self> {
            Some(self.checked_div_rem_ilimb(n)?.0)
        }

        /// Get the remainder of our big integer divided by a signed
        /// limb, returning None on overflow or division by 0.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn checked_rem_ilimb(self, n: $crate::ILimb) -> Option<$crate::ILimb> {
            Some(self.checked_div_rem_ilimb(n)?.1)
        }
    };

    (@all) => {
        int_limb_ops_define!();
        int_limb_ops_define!(@wrapping);
        int_limb_ops_define!(@overflowing);
        int_limb_ops_define!(@checked);
    };
}

macro_rules! int_traits_define {
    (type => $t:ty,unsigned_type => $u_t:ty) => {
        traits_define!($t);
        shift_define! { @256 base => $t, impl => $u_t }
        shift_define! { base => $t, impl => $u_t }

        impl Neg for $t {
            type Output = Self;

            #[inline(always)]
            fn neg(self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_neg()
                } else {
                    match self.checked_neg() {
                        Some(v) => v,
                        _ => core::panic!("attempt to negate with overflow"),
                    }
                }
            }
        }

        ref_trait_define!($t, Neg, neg);

        impl core::str::FromStr for $t {
            type Err = $crate::ParseIntError;

            /// Parses a string s to return a value of this type.
            ///
            /// This is not optimized, since all optimization is done in
            /// theimplementation.
            #[inline]
            fn from_str(src: &str) -> Result<Self, $crate::ParseIntError> {
                // up to 39 digits can be stored in a `u128`, so less is always valid
                // meanwhile, 78 is good for all 256-bit integers. 32-bit architectures
                // on average have poor support for 128-bit operations so we try to use `u64`.
                if (cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32"))
                    && src.len() < 19
                {
                    Ok(Self::from_i64(i64::from_str(src)?))
                } else if src.len() < 39 {
                    Ok(Self::from_i128(i128::from_str(src)?))
                } else {
                    Self::from_str_radix(src, 10)
                }
            }
        }

        impl core::fmt::Binary for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                // NOTE: Binary for negative numbers uses wrapping formats.
                core::fmt::Binary::fmt(&self.as_unsigned(), f)
            }
        }

        impl core::fmt::Display for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                if self.is_negative() {
                    write!(f, "-")?;
                } else if f.sign_plus() {
                    write!(f, "+")?;
                }
                core::fmt::Display::fmt(&self.unsigned_abs(), f)
            }
        }

        impl core::fmt::LowerExp for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                if self.is_negative() {
                    write!(f, "-")?;
                } else if f.sign_plus() {
                    write!(f, "+")?;
                }
                core::fmt::LowerExp::fmt(&self.unsigned_abs(), f)
            }
        }

        impl core::fmt::LowerHex for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                // NOTE: LowerHex for negative numbers uses wrapping formats.
                core::fmt::LowerHex::fmt(&self.as_unsigned(), f)
            }
        }

        impl core::fmt::Octal for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                // NOTE: Octal for negative numbers uses wrapping formats.
                core::fmt::Octal::fmt(&self.as_unsigned(), f)
            }
        }

        impl core::fmt::UpperExp for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                if self.is_negative() {
                    write!(f, "-")?;
                } else if f.sign_plus() {
                    write!(f, "+")?;
                }
                core::fmt::UpperExp::fmt(&self.unsigned_abs(), f)
            }
        }

        impl core::fmt::UpperHex for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                // NOTE: UpperHex for negative numbers uses wrapping formats.
                core::fmt::UpperHex::fmt(&self.as_unsigned(), f)
            }
        }

        from_trait_define!($t, i8, from_i8);
        from_trait_define!($t, i16, from_i16);
        from_trait_define!($t, i32, from_i32);
        from_trait_define!($t, i64, from_i64);
        from_trait_define!($t, i128, from_i128);

        impl TryFrom<$u_t> for $t {
            type Error = TryFromIntError;

            #[inline(always)]
            fn try_from(u: $u_t) -> Result<Self, TryFromIntError> {
                if u < Self::MAX.as_unsigned() {
                    Ok(u.as_signed())
                } else {
                    Err(TryFromIntError {})
                }
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! int_impl_define {
    (
        self => $self:ty,
        unsigned_t => $u_t:ty,
        unsigned_wide_t => $wide_u_t:ty,
        signed_wide_t => $wide_s_t:ty,
        bits => $bits:expr,
        max_digits => $max_digits:expr,
        kind => $kind:ident,
        short_circuit => $short_circuit:tt,
    ) => {
        int_associated_consts_define!(
            bits => $bits,
            max_digits => $max_digits,
            wide_type => $wide_s_t,
        );
        int_bitops_define!(unsigned_type => $u_t, wide_type => $wide_s_t);
        int_byte_order_define!(unsigned_type => $u_t, wide_type => $wide_s_t);
        int_cmp_define!(
            low_type => $wide_u_t,
            high_type => $wide_s_t,
            short_circuit => $short_circuit,
        );
        int_casts_define!(
            unsigned_type => $u_t,
            bits => $bits,
            wide_type => $wide_s_t,
            kind => $kind,
        );
        int_extensions_define!(unsigned_type => $u_t, wide_type => $wide_s_t);
        int_ops_define!(unsigned_type => $u_t, wide_type => $wide_s_t);
        int_bigint_define!(unsigned_type => $u_t, wide_type => $wide_s_t);
        int_wrapping_define!(unsigned_type => $u_t, wide_type => $wide_s_t);
        int_overflowing_define!(unsigned_type => $u_t, wide_type => $wide_s_t);
        int_saturating_define!(unsigned_type => $u_t, wide_type => $wide_s_t);
        int_checked_define!(unsigned_type => $u_t, wide_type => $wide_s_t);
        int_strict_define!(unsigned_type => $u_t, wide_type => $wide_s_t);
        int_unchecked_define!(unsigned_type => $u_t, wide_type => $wide_s_t);
        int_unbounded_define!(unsigned_type => $u_t, wide_type => $wide_s_t);
        int_limb_ops_define!(@all);

        from_str_radix_define!(true);
        to_str_radix_define!(true);
    };
}
