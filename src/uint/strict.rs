//! Strict arithemetic operations, which always panic on overflow.

#[rustfmt::skip]
macro_rules! define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        $crate::shared::strict::define!(type => $s_t, wide_type => $wide_t);

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
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
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
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
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
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
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
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
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
        ///
        /// <div class="warning">
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        /// </div>
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
    };
}

pub(crate) use define;
