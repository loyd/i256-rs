//! Overflowing mathmetical operations, which wrap on overflow.

#[rustfmt::skip]
macro_rules! define {
    (type => $t:ty,wide_type => $wide_t:ty) => {
        /// Wrapping (modular) exponentiation. Computes `self.pow(exp)`,
        /// wrapping around at the boundary of the type.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($wide_t, wrapping_pow)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_pow(self, mut exp: u32) -> Self {
            if exp == 0 {
                return Self::from_u8(1);
            }
            let mut base = self;
            let mut acc = Self::from_u8(1);

            // NOTE: The exponent can never go to 0.
            loop {
                if (exp & 1) == 1 {
                    acc = acc.wrapping_mul(base);
                    // since exp!=0, finally the exp must be 1.
                    if exp == 1 {
                        return acc;
                    }
                }
                exp /= 2;
                base = base.wrapping_mul(base);
                debug_assert!(exp != 0, "logic error in exponentiation, will infinitely loop");
            }
        }
    };
}

pub(crate) use define;
