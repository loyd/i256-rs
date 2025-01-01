//! Custom integer extensions for ergonomics.

macro_rules! define {
    (
        high_type => $hi_t:ty $(,)?
    ) => {
        $crate::shared::extensions::define!(high_type => $hi_t);

        /// Get the lower half of the integer, that is, the bits in `[0, BITS/2)`.
        #[inline(always)]
        pub const fn low(self) -> Self {
            let limbs = self.to_ne_limbs();
            let mut r = [0; Self::LIMBS];
            let half = Self::LIMBS / 2;
            let mut i = 0;
            while i < half {
                ne_index!(r[i] = ne_index!(limbs[i]));
                i += 1;
            }
            Self::from_ne_limbs(r)
        }

        /// Get the upper half of the integer, that is, the bits in `[BITS/2, BITS)`,
        /// shifted into place to the lower half.
        #[inline(always)]
        pub const fn high(self) -> Self {
            let limbs = self.to_ne_limbs();
            let mut r = [0; Self::LIMBS];
            let half = Self::LIMBS / 2;
            let mut i = 0;
            while i < half {
                ne_index!(r[i] = ne_index!(limbs[i + half]));
                i += 1;
            }
            Self::from_ne_limbs(r)
        }

        /// Multiply two values, grabbing the high half of the product.
        ///
        /// Naively, this is [`Self::widening_mul`] and then taking the
        /// high half, however, this can use custom optimizations.
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn high_mul(self, rhs: Self) -> Self {
            // Extract high-and-low masks.
            let x1 = self.high();
            let x0 = self.low();
            let y1 = rhs.high();
            let y0 = rhs.low();

            let w0 = x0.wrapping_mul(y0);
            let m = x0.wrapping_mul(y1).wrapping_add(w0.high());
            let w1 = m.low();
            let w2 = m.high();

            let w3 = x1.wrapping_mul(y0).wrapping_add(w1).high();

            x1.wrapping_mul(y1).wrapping_add(w2).wrapping_add(w3)
        }
    };
}

pub(crate) use define;
