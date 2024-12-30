//! Strict arithemetic operations, which always panic on overflow.

#[rustfmt::skip]
macro_rules! define {
    (unsigned_type => $u_t:ty, wide_type => $wide_t:ty) => {
        $crate::shared::strict::define!(type => $u_t, wide_type => $wide_t);

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

pub(crate) use define;
