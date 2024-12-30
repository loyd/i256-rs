//! Overflowing mathmetical operations, which wrap on overflow.

#[rustfmt::skip]
macro_rules! define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        $crate::shared::wrapping::define!(type => $u_t, wide_type => $wide_t);

        /// Wrapping (modular) addition. Computes `self + rhs`, wrapping around at
        /// the boundary of the type.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_add`].")]
        #[inline(always)]
        pub const fn wrapping_add(self, rhs: Self) -> Self {
            let result = $crate::math::add::wrapping_signed(&self.to_ne_limbs(), &rhs.to_ne_limbs());
            Self::from_ne_limbs(result)
        }

        /// Wrapping (modular) subtraction. Computes `self - rhs`, wrapping around
        /// at the boundary of the type.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_sub`].")]
        #[inline(always)]
        pub const fn wrapping_sub(self, rhs: Self) -> Self {
            let result = $crate::math::sub::wrapping_signed(&self.to_ne_limbs(), &rhs.to_ne_limbs());
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
            let limbs = $crate::math::mul::wrapping_signed(&self.to_ne_limbs(), &rhs.to_ne_limbs());
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
            let (div, rem) = $crate::math::div::full(&x, &y);
            let mut div = <$u_t>::from_le_limbs(div).as_signed();
            let mut rem = <$u_t>::from_le_limbs(rem).as_signed();

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

pub(crate) use define;
