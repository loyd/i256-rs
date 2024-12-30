//! Unbounded operations, returning 0 on overflow.

#[rustfmt::skip]
macro_rules! define {
    (type => $t:ty,wide_type => $wide_t:ty) => {
        /// Unbounded shift left. Computes `self << rhs`, without bounding the value
        /// of `rhs`.
        ///
        /// If `rhs` is larger or equal to the number of bits in `self`,
        /// the entire value is shifted out, and `0` is returned.
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub const fn unbounded_shl(self, rhs: u32) -> Self {
            if rhs < Self::BITS {
                self.wrapping_shl(rhs)
            } else {
                Self::from_u8(0)
            }
        }

        /// Unbounded shift right. Computes `self >> rhs`, without bounding the
        /// value of `rhs`.
        ///
        /// If `rhs` is larger or equal to the number of bits in `self`,
        /// the entire value is shifted out, and `0` is returned.
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub const fn unbounded_shr(self, rhs: u32) -> Self {
            if rhs < Self::BITS {
                self.wrapping_shr(rhs)
            } else {
                Self::from_u8(0)
            }
        }
    };
}

pub(crate) use define;
