//! Overflowing mathmetical operations, which wrap and return if it overflowed.

#[rustfmt::skip]
macro_rules! define {
    (type => $t:ty,wide_type => $wide_t:ty) => {
        /// Raises self to the power of `exp`, using exponentiation by squaring,
        /// returning the value.
        ///
        /// Returns a tuple of the exponentiation along with a bool indicating
        /// whether an overflow happened.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::overflowing_pow`].")]
        #[inline]
        pub const fn overflowing_pow(self, mut exp: u32) -> (Self, bool) {
            if exp == 0 {
                return (Self::from_u8(1), false);
            }
            let mut base = self;
            let mut acc = Self::from_u8(1);
            let mut overflowed = false;
            let mut r: (Self, bool);

            // NOTE: The exponent can never go to 0.
            loop {
                if (exp & 1) == 1 {
                    r = acc.overflowing_mul(base);
                    // since exp!=0, finally the exp must be 1.
                    if exp == 1 {
                        r.1 |= overflowed;
                        return r;
                    }
                    acc = r.0;
                    overflowed |= r.1;
                }
                exp /= 2;
                r = base.overflowing_mul(base);
                base = r.0;
                overflowed |= r.1;
                debug_assert!(exp != 0, "logic error in exponentiation, will infinitely loop");
            }
        }

        /// Get the quotient and remainder of our big integer division,
        /// returning the value and if overflow occurred.
        ///
        /// This allows storing of both the quotient and remainder without
        /// making repeated calls.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        #[inline]
        pub fn overflowing_div_rem(self, n: Self) -> ((Self, Self), bool) {
            if self.is_div_overflow(n) {
                ((self, Self::from_u8(0)), true)
            } else {
                (self.wrapping_div_rem(n), false)
            }
        }
    };
}

pub(crate) use define;
