//! Macros for unsigned, fixed width big integers.
//!
//! A lot of these depend on methods from other defines, so if
//! implementing your own produces many errors, look through
//! and custom implement the types required.

/// Define the high and low implementations for 4 limb implementations.
///
/// This is specific for **ONLY** our 256-bit integers (4x 64-bit limbs).
macro_rules! uint_high_low_define {
    (
        self => $t:ty,
        low_type => $lo_t:ty,
        high_type => $hi_t:ty,
        kind => $kind:ident $(,)?
    ) => {
        high_low_define!(
            self => $t,
            low_type => $lo_t,
            high_type => $hi_t,
            kind => $kind,
        );
    };
}

macro_rules! uint_associated_consts_define {
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
            high_type => $crate::ULimb,
        );

        #[doc = concat!("New code should prefer to use  [`", stringify!($wide_t), "::MIN`] instead.")]
        ///
        /// Returns the smallest value that can be represented by this integer type.
        #[doc = concat!("See [`", stringify!($wide_t), "::min_value`].")]
        #[inline(always)]
        #[deprecated]
        pub const fn min_value() -> Self {
            Self::from_ne_limbs([0; Self::LIMBS])
        }

        #[doc = concat!("New code should prefer to use  [`", stringify!($wide_t), "::MAX`] instead.")]
        ///
        /// Returns the largest value that can be represented by this integer type.
        #[doc = concat!("See [`", stringify!($wide_t), "::max_value`].")]
        #[inline(always)]
        #[deprecated]
        pub const fn max_value() -> Self {
            Self::from_ne_limbs([$crate::ULimb::MAX; Self::LIMBS])
        }
    };
}

macro_rules! uint_cmp_define {
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

macro_rules! uint_bitops_define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        bitops_define!(type => $s_t, wide_type => $wide_t);
    };
}

macro_rules! uint_byte_order_define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        byte_order_define!(type => $s_t, wide_type => $wide_t);
    };
}

macro_rules! uint_casts_define {
    (
        signed_type => $s_t:ty,
        bits => $bits:expr,
        wide_type => $wide_t:ty,
        kind => $kind:ident $(,)?
    ) => {
        casts_define!(
            bits => $bits,
            kind => $kind,
        );

        /// Returns the bit pattern of `self` reinterpreted as a signed integer of
        /// the same size.
        ///
        /// This produces the same result as an `as` cast, but ensures that the
        /// bit-width remains the same.
        #[doc = concat!("See [`", stringify!($wide_t), "::cast_signed`].")]
        #[inline(always)]
        pub const fn cast_signed(self) -> $s_t {
            self.as_signed()
        }
    };
}

macro_rules! uint_extensions_define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        extensions_define!(type => $s_t, wide_type => $wide_t);
    };
}

macro_rules! uint_ops_define {
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

        ops_define!(type => $s_t, wide_type => $wide_t);

        /// Performs Euclidean division.
        ///
        /// Since, for the positive integers, all common
        /// definitions of division are equal, this
        /// is exactly equal to `self / rhs`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
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
        #[doc = concat!("See [`", stringify!($wide_t), "::div_ceil`].")]
        #[inline]
        pub fn div_ceil(self, rhs: Self) -> Self {
            let (d, r) = self.wrapping_div_rem(rhs);
            if r.gt_const(Self::from_u8(0)) {
                // NOTE: This can't overflow
                d.wrapping_add(Self::from_u8(1))
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
        /// See [`u128::is_power_of_two`].
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

macro_rules! uint_bigint_define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        bigint_define!(type => $s_t, wide_type => $wide_t);
    };
}

macro_rules! uint_wrapping_define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        wrapping_define!(type => $s_t, wide_type => $wide_t);
        /// Div/Rem operation on a 256-bit integer.
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
            let x = self.to_le_limbs();
            let y = n.to_le_limbs();

            let (div, rem) = math::div_rem_full(&x, &y);
            let div = Self::from_le_limbs(div);
            let rem = Self::from_le_limbs(rem);

            (div, rem)
        }

        /// Wrapping (modular) division. Computes `self / rhs`.
        ///
        /// Wrapped division on unsigned types is just normal division. There's
        /// no way wrapping could ever happen. This function exists so that all
        /// operations are accounted for in the wrapping operations.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_div`].")]
        #[inline(always)]
        pub fn wrapping_div(self, rhs: Self) -> Self {
            self.wrapping_div_rem(rhs).0
        }

        /// Wrapping Euclidean division. Computes `self.div_euclid(rhs)`.
        ///
        /// Wrapped division on unsigned types is just normal division. There's
        /// no way wrapping could ever happen. This function exists so that all
        /// operations are accounted for in the wrapping operations. Since, for
        /// the positive integers, all common definitions of division are equal,
        /// this is exactly equal to `self.wrapping_div(rhs)`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_div_euclid`].")]
        #[inline(always)]
        pub fn wrapping_div_euclid(self, rhs: Self) -> Self {
            self.wrapping_div(rhs)
        }

        /// Wrapping (modular) remainder. Computes `self % rhs`.
        ///
        /// Wrapped remainder calculation on unsigned types is just the regular
        /// remainder calculation. There's no way wrapping could ever happen.
        /// This function exists so that all operations are accounted for in the
        /// wrapping operations.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_rem`].")]
        #[inline(always)]
        pub fn wrapping_rem(self, rhs: Self) -> Self {
            self.wrapping_div_rem(rhs).1
        }

        /// Wrapping Euclidean modulo. Computes `self.rem_euclid(rhs)`.
        ///
        /// Wrapped modulo calculation on unsigned types is just the regular
        /// remainder calculation. There's no way wrapping could ever happen.
        /// This function exists so that all operations are accounted for in the
        /// wrapping operations. Since, for the positive integers, all common
        /// definitions of division are equal, this is exactly equal to
        /// `self.wrapping_rem(rhs)`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_rem_euclid`].")]
        #[inline(always)]
        pub fn wrapping_rem_euclid(self, rhs: Self) -> Self {
            self.wrapping_rem(rhs)
        }

        /// Wrapping (modular) negation. Computes `-self`,
        /// wrapping around at the boundary of the type.
        ///
        /// Since unsigned types do not have negative equivalents
        /// all applications of this function will wrap (except for `-0`).
        /// For values smaller than the corresponding signed type's maximum
        /// the result is the same as casting the corresponding signed value.
        /// Any larger values are equivalent to `MAX + 1 - (val - MAX - 1)` where
        /// `MAX` is the corresponding signed type's maximum.
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_neg`].")]
        #[inline(always)]
        pub const fn wrapping_neg(self) -> Self {
            Self::MIN.wrapping_sub(self)
        }

        /// Returns the smallest power of two greater than or equal to `n`. If
        /// the next power of two is greater than the type's maximum value,
        /// the return value is wrapped to `0`.
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_next_power_of_two`].")]
        #[inline]
        pub const fn wrapping_next_power_of_two(self) -> Self {
            self.one_less_than_next_power_of_two().wrapping_add(Self::from_u8(1))
        }
    };
}

macro_rules! uint_overflowing_define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        overflowing_define!(type => $s_t, wide_type => $wide_t);

        /// Calculates `self` + `rhs` with a signed `rhs`.
        ///
        /// Returns a tuple of the addition along with a boolean indicating
        /// whether an arithmetic overflow would occur. If an overflow would
        /// have occurred then the wrapped value is returned.
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_add_signed`].")]
        #[inline(always)]
        pub const fn overflowing_add_signed(self, rhs: $s_t) -> (Self, bool) {
            let is_negative = rhs.is_negative();
            let (r, overflowed) = self.overflowing_add(Self::from_signed(rhs));
            (r, overflowed ^ is_negative)
        }

        /// Calculates `self` - `rhs` with a signed `rhs`
        ///
        /// Returns a tuple of the subtraction along with a boolean indicating
        /// whether an arithmetic overflow would occur. If an overflow would
        /// have occurred then the wrapped value is returned.
        #[inline]
        #[must_use]
        pub const fn overflowing_sub_signed(self, rhs: $s_t) -> (Self, bool) {
            let (res, overflow) = self.overflowing_sub(rhs.as_unsigned());
            (res, overflow ^ (rhs.is_negative()))
        }

        /// Calculates the divisor when `self` is divided by `rhs`.
        ///
        /// Returns a tuple of the divisor along with a boolean indicating
        /// whether an arithmetic overflow would occur. Note that for unsigned
        /// integers overflow never occurs, so the second value is always
        /// `false`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_div`].")]
        #[inline(always)]
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
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_div_euclid`].")]
        #[inline(always)]
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
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_rem`].")]
        #[inline(always)]
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
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_rem_euclid`].")]
        #[inline(always)]
        pub fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) {
            self.overflowing_rem(rhs)
        }
    };
}

macro_rules! uint_saturating_define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        saturating_define!(type => $s_t, wide_type => $wide_t);

        /// Saturating integer addition. Computes `self + rhs`, saturating at
        /// the numeric bounds instead of overflowing.
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_add`].")]
        #[inline(always)]
        pub const fn saturating_add(self, rhs: Self) -> Self {
            match self.checked_add(rhs) {
                Some(v) => v,
                None => Self::MAX,
            }
        }

        /// Saturating addition with a signed integer. Computes `self + rhs`,
        /// saturating at the numeric bounds instead of overflowing.
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_add_signed`].")]
        #[inline]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_sub`].")]
        #[inline(always)]
        pub const fn saturating_sub(self, rhs: Self) -> Self {
            match self.checked_sub(rhs) {
                Some(v) => v,
                None => Self::MIN,
            }
        }

        /// Saturating integer multiplication. Computes `self * rhs`,
        /// saturating at the numeric bounds instead of overflowing.
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_mul`].")]
        #[inline(always)]
        pub const fn saturating_mul(self, rhs: Self) -> Self {
            match self.checked_mul(rhs) {
                Some(v) => v,
                None => Self::MAX,
            }
        }

        /// Saturating integer division. Computes `self / rhs`, saturating at the
        /// numeric bounds instead of overflowing.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_div`].")]
        #[inline(always)]
        pub fn saturating_div(self, rhs: Self) -> Self {
            // on unsigned types, there is no overflow in integer division
            self.wrapping_div(rhs)
        }

        /// Saturating integer exponentiation. Computes `self.pow(exp)`,
        /// saturating at the numeric bounds instead of overflowing.
        #[doc = concat!("See [`", stringify!($wide_t), "::saturating_pow`].")]
        #[inline]
        pub const fn saturating_pow(self, exp: u32) -> Self {
            match self.checked_pow(exp) {
                Some(x) => x,
                None => Self::MAX,
            }
        }
    };
}

macro_rules! uint_checked_define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        checked_define!(type => $s_t, wide_type => $wide_t);

        /// Checked addition with a signed integer. Computes `self + rhs`,
        /// returning `None` if overflow occurred.
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_add_signed`].")]
        #[inline(always)]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_neg`].")]
        #[inline(always)]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_ilog`].")]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_next_multiple_of`].")]
        #[inline]
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
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_next_power_of_two`].")]
        #[inline]
        pub const fn checked_next_power_of_two(self) -> Option<Self> {
            self.one_less_than_next_power_of_two().checked_add(Self::from_u8(1))
        }
    };
}

macro_rules! uint_strict_define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        strict_define!(type => $s_t, wide_type => $wide_t);

        /// Strict addition with a signed integer. Computes `self + rhs`,
        /// panicking if overflow occurred.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_add_signed`].")]
        #[inline]
        #[must_use]
        pub const fn strict_add_signed(self, rhs: $s_t) -> Self {
            match self.checked_add_signed(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to add with overflow"),
            }
        }

        /// Strict integer division. Computes `self / rhs`.
        ///
        /// Strict division on unsigned types is just normal division. There's no
        /// way overflow could ever happen. This function exists so that all
        /// operations are accounted for in the strict operations.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_div`].")]
        #[must_use]
        #[inline(always)]
        pub fn strict_div(self, rhs: Self) -> Self {
            match self.checked_div(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to divide by zero"),
            }
        }

        /// Strict integer remainder. Computes `self % rhs`.
        ///
        /// Strict remainder calculation on unsigned types is just the regular
        /// remainder calculation. There's no way overflow could ever happen.
        /// This function exists so that all operations are accounted for in the
        /// strict operations.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_rem`].")]
        #[must_use]
        #[inline(always)]
        pub fn strict_rem(self, rhs: Self) -> Self {
            match self.checked_rem(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to divide by zero"),
            }
        }

        /// Strict Euclidean division. Computes `self.div_euclid(rhs)`.
        ///
        /// Strict division on unsigned types is just normal division. There's no
        /// way overflow could ever happen. This function exists so that all
        /// operations are accounted for in the strict operations. Since, for the
        /// positive integers, all common definitions of division are equal, this
        /// is exactly equal to `self.strict_div(rhs)`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_div_euclid`].")]
        #[must_use]
        #[inline(always)]
        pub fn strict_div_euclid(self, rhs: Self) -> Self {
            match self.checked_div_euclid(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to divide by zero"),
            }
        }

        /// Strict Euclidean modulo. Computes `self.rem_euclid(rhs)`.
        ///
        /// Strict modulo calculation on unsigned types is just the regular
        /// remainder calculation. There's no way overflow could ever happen.
        /// This function exists so that all operations are accounted for in the
        /// strict operations. Since, for the positive integers, all common
        /// definitions of division are equal, this is exactly equal to
        /// `self.strict_rem(rhs)`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_rem_euclid`].")]
        #[must_use]
        #[inline(always)]
        pub fn strict_rem_euclid(self, rhs: Self) -> Self {
            match self.checked_rem_euclid(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to divide by zero"),
            }
        }

        /// Strict negation. Computes `-self`, panicking unless `self ==
        /// 0`.
        ///
        /// Note that negating any positive integer will overflow.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_neg`].")]
        #[inline]
        #[must_use]
        pub const fn strict_neg(self) -> Self {
            match self.checked_neg() {
                Some(v) => v,
                None => core::panic!("attempt to negate with overflow"),
            }
        }
    };
}

macro_rules! uint_unchecked_define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        unchecked_define!(type => $s_t, wide_type => $wide_t);
    };
}

macro_rules! uint_unbounded_define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        unbounded_define!(type => $s_t, wide_type => $wide_t);
    };
}

macro_rules! uint_limb_ops_define {
    () => {
        limb_ops_define!();
    };

    (@wrapping) => {
        limb_ops_define!(@wrapping);
    };

    (@overflowing) => {
        limb_ops_define!(@overflowing);
    };

    (@checked) => {
        limb_ops_define!(@checked);
    };

    (@all) => {
        uint_limb_ops_define!();
        uint_limb_ops_define!(@wrapping);
        uint_limb_ops_define!(@overflowing);
        uint_limb_ops_define!(@checked);
    };
}

macro_rules! uint_wide_ops_define {
    () => {
        wide_ops_define!();
    };

    (@wrapping) => {
        wide_ops_define!(@wrapping);
    };

    (@overflowing) => {
        wide_ops_define!(@overflowing);
    };

    (@checked) => {
        wide_ops_define!(@checked);
    };

    (@all) => {
        uint_wide_ops_define!();
        uint_wide_ops_define!(@wrapping);
        uint_wide_ops_define!(@overflowing);
        uint_wide_ops_define!(@checked);
    };
}

macro_rules! uint_traits_define {
    (type => $t:ty,signed_type => $s_t:ty) => {
        traits_define!($t);
        shift_define! { @256 base => $t, impl => $s_t }
        shift_define! { base => $t, impl => $s_t }

        impl core::fmt::Binary for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 2);
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                if f.alternate() {
                    f.write_str("0b")?;
                }
                if let Some(width) = f.width() {
                    let c = f.fill();
                    let pad = width.saturating_sub(bytes.len());
                    for _ in 0..pad {
                        write!(f, "{c}")?;
                    }
                }
                core::write!(f, "{}", formatted)
            }
        }

        impl core::fmt::Display for $t {
            #[inline]
            #[allow(clippy::bind_instead_of_map)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 10);
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                core::write!(f, "{}", formatted)
            }
        }

        impl core::fmt::LowerHex for u256 {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let count = self.to_str_radix(&mut buffer, 16).len();
                let lower = buffer.map(|x| x.to_ascii_lowercase());
                let bytes = &lower[buffer.len() - count..];
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                if f.alternate() {
                    f.write_str("0x")?;
                }
                if let Some(width) = f.width() {
                    let c = f.fill();
                    let pad = width.saturating_sub(count);
                    for _ in 0..pad {
                        write!(f, "{c}")?;
                    }
                }
                f.write_str(formatted)
            }
        }

        impl core::fmt::UpperHex for u256 {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let count = self.to_str_radix(&mut buffer, 16).len();
                let upper = buffer.map(|x| x.to_ascii_uppercase());
                let bytes = &upper[buffer.len() - count..];
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                if f.alternate() {
                    f.write_str("0x")?;
                }
                if let Some(width) = f.width() {
                    let c = f.fill();
                    let pad = width.saturating_sub(count);
                    for _ in 0..pad {
                        write!(f, "{c}")?;
                    }
                }
                f.write_str(formatted)
            }
        }

        impl core::fmt::LowerExp for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 10);
                let formatted = core::str::from_utf8(&bytes[1..]);
                let formatted = formatted.or_else(|_| Err(core::fmt::Error))?;
                core::write!(f, "{}.{}e{}", bytes[0] as char, formatted, bytes.len() - 1)
            }
        }

        impl core::fmt::UpperExp for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 10);
                let formatted = core::str::from_utf8(&bytes[1..]);
                let formatted = formatted.or_else(|_| Err(core::fmt::Error))?;
                core::write!(f, "{}.{}E{}", bytes[0] as char, formatted, bytes.len() - 1)
            }
        }

        impl core::fmt::Octal for u256 {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 8);
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                if f.alternate() {
                    f.write_str("0o")?;
                }
                if let Some(width) = f.width() {
                    let c = f.fill();
                    let pad = width.saturating_sub(bytes.len());
                    for _ in 0..pad {
                        write!(f, "{c}")?;
                    }
                }
                core::write!(f, "{}", formatted)
            }
        }

        impl core::str::FromStr for $t {
            type Err = $crate::ParseIntError;

            /// Parses a string s to return a value of this type.
            ///
            /// This is not optimized, since all optimization is done in
            /// the lexical implementation.
            #[inline]
            fn from_str(src: &str) -> Result<Self, $crate::ParseIntError> {
                // up to 39 digits can be stored in a `u128`, so less is always valid
                // meanwhile, 78 is good for all 256-bit integers. 32-bit architectures
                // on average have poor support for 128-bit operations so we try to use `u64`.
                if (cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32"))
                    && src.len() < 20
                {
                    Ok(Self::from_u64(u64::from_str(src)?))
                } else if src.len() < 39 {
                    Ok(Self::from_u128(u128::from_str(src)?))
                } else {
                    Self::from_str_radix(src, 10)
                }
            }
        }

        try_from_define! { base => $t, from => i8 i16 i32 i64 i128 isize }

        impl TryFrom<$s_t> for $t {
            type Error = $crate::TryFromIntError;

            #[inline(always)]
            fn try_from(u: $s_t) -> Result<Self, $crate::TryFromIntError> {
                if !u.is_negative() {
                    Ok(u.as_unsigned())
                } else {
                    Err($crate::TryFromIntError {})
                }
            }
        }
    };
}

#[doc(hidden)]
#[macro_export]
macro_rules! uint_impl_define {
    (
        self => $self:ty,
        signed_t => $s_t:ty,
        signed_wide_t => $wide_s_t:ty,
        unsigned_wide_t => $wide_u_t:ty,
        bits => $bits:expr,
        max_digits => $max_digits:expr,
        kind => $kind:ident,
        short_circuit => $short_circuit:tt $(,)?
    ) => {
        uint_associated_consts_define!(
            bits => $bits,
            max_digits => $max_digits,
            wide_type => $wide_u_t,
        );
        uint_bitops_define!(signed_type => $s_t, wide_type => $wide_u_t);
        uint_byte_order_define!(signed_type => $s_t, wide_type => $wide_u_t);
        uint_high_low_define!(
            self => $self,
            low_type => $wide_u_t,
            high_type => $wide_u_t,
            kind => $kind,
        );
        uint_cmp_define!(
            low_type => $wide_u_t,
            high_type => $wide_u_t,
            short_circuit => $short_circuit,
        );
        uint_casts_define!(
            signed_type => $s_t,
            bits => $bits,
            wide_type => $wide_u_t,
            kind => $kind,
        );
        uint_extensions_define!(signed_type => $s_t, wide_type => $wide_u_t);
        uint_ops_define!(signed_type => $s_t, wide_type => $wide_u_t);
        uint_bigint_define!(signed_type => $s_t, wide_type => $wide_u_t);
        uint_wrapping_define!(signed_type => $s_t, wide_type => $wide_u_t);
        uint_overflowing_define!(signed_type => $s_t, wide_type => $wide_u_t);
        uint_saturating_define!(signed_type => $s_t, wide_type => $wide_u_t);
        uint_checked_define!(signed_type => $s_t, wide_type => $wide_u_t);
        uint_strict_define!(signed_type => $s_t, wide_type => $wide_u_t);
        uint_unchecked_define!(signed_type => $s_t, wide_type => $wide_u_t);
        uint_unbounded_define!(signed_type => $s_t, wide_type => $wide_u_t);
        uint_limb_ops_define!(@all);
        uint_wide_ops_define!(@all);
    };
}
