//! Strict arithemetic operations, which always panic on overflow.

#[rustfmt::skip]
macro_rules! define {
    (type => $t:ty,wide_type => $wide_t:ty) => {
        /// Strict integer addition. Computes `self + rhs`, panicking
        /// if overflow occurred.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_add`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub const fn strict_add(self, rhs: Self) -> Self {
            match self.checked_add(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to add with overflow"),
            }
        }

        /// Strict integer subtraction. Computes `self - rhs`, panicking if
        /// overflow occurred.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_sub`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub const fn strict_sub(self, rhs: Self) -> Self {
            match self.checked_sub(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to subtract with overflow"),
            }
        }

        /// Strict integer multiplication. Computes `self * rhs`, panicking if
        /// overflow occurred.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_mul`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub const fn strict_mul(self, rhs: Self) -> Self {
            match self.checked_mul(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to subtract with overflow"),
            }
        }

        /// Strict exponentiation. Computes `self.pow(exp)`, panicking if
        /// overflow occurred.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_pow`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub const fn strict_pow(self, rhs: u32) -> Self {
            match self.checked_pow(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to multiply with overflow"),
            }
        }

        /// Strict shift left. Computes `self << rhs`, panicking if `rhs` is larger
        /// than or equal to the number of bits in `self`.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_shl`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub const fn strict_shl(self, rhs: u32) -> Self {
            match self.checked_shl(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to shift left with overflow"),
            }
        }

        /// Strict shift right. Computes `self >> rhs`, panicking `rhs` is
        /// larger than or equal to the number of bits in `self`.
        ///
        /// # Panics
        ///
        /// ## Overflow behavior
        ///
        /// This function will always panic on overflow, regardless of whether
        /// overflow checks are enabled.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::strict_shr`].")]
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
        #[inline]
        #[must_use]
        pub const fn strict_shr(self, rhs: u32) -> Self {
            match self.checked_shr(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to shift right with overflow"),
            }
        }
    };
}

pub(crate) use define;
