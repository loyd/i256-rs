//! Unchecked arithmetic operations.
//!
//! On overflow or other unexpected cases, this results in
//! undefined behavior.

#[rustfmt::skip]
macro_rules! define {
    (type => $t:ty,wide_type => $wide_t:ty) => {
        /// Unchecked integer addition. Computes `self + rhs`, assuming overflow
        /// cannot occur.
        ///
        /// Calling `x.unchecked_add(y)` is semantically equivalent to calling
        /// `x.`[`checked_add`]`(y).`[`unwrap_unchecked`]`()`.
        ///
        /// If you're just trying to avoid the panic in debug mode, then **do not**
        /// use this.  Instead, you're looking for [`wrapping_add`].
        ///
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        ///
        /// # Safety
        ///
        /// This results in undefined behavior when the value overflows.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::unchecked_add`].")]
        ///
        /// [`checked_add`]: Self::checked_add
        /// [`wrapping_add`]: Self::wrapping_add
        /// [`unwrap_unchecked`]: Option::unwrap_unchecked
        #[must_use]
        #[inline(always)]
        pub unsafe fn unchecked_add(self, rhs: Self) -> Self {
            match self.checked_add(rhs) {
                Some(value) => value,
                // SAFETY: this is guaranteed to be safe by the caller.
                None => unsafe { core::hint::unreachable_unchecked() },
            }
        }

        /// Unchecked integer subtraction. Computes `self - rhs`, assuming overflow
        /// cannot occur.
        ///
        /// Calling `x.unchecked_sub(y)` is semantically equivalent to calling
        /// `x.`[`checked_sub`]`(y).`[`unwrap_unchecked`]`()`.
        ///
        /// If you're just trying to avoid the panic in debug mode, then **do not**
        /// use this.  Instead, you're looking for [`wrapping_sub`].
        ///
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        ///
        /// # Safety
        ///
        /// This results in undefined behavior when the value overflows.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::unchecked_sub`].")]
        ///
        /// [`checked_sub`]: Self::checked_sub
        /// [`wrapping_sub`]: Self::wrapping_sub
        /// [`unwrap_unchecked`]: Option::unwrap_unchecked
        #[must_use]
        #[inline(always)]
        pub unsafe fn unchecked_sub(self, rhs: Self) -> Self {
            match self.checked_sub(rhs) {
                Some(value) => value,
                // SAFETY: this is guaranteed to be safe by the caller.
                None => unsafe { core::hint::unreachable_unchecked() },
            }
        }

        /// Unchecked integer multiplication. Computes `self * rhs`, assuming
        /// overflow cannot occur.
        ///
        /// Calling `x.unchecked_mul(y)` is semantically equivalent to calling
        /// `x.`[`checked_mul`]`(y).`[`unwrap_unchecked`]`()`.
        ///
        /// If you're just trying to avoid the panic in debug mode, then **do not**
        /// use this.  Instead, you're looking for [`wrapping_mul`].
        ///
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        ///
        /// # Safety
        ///
        /// This results in undefined behavior when the value overflows.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::unchecked_mul`].")]
        ///
        /// [`wrapping_mul`]: Self::wrapping_mul
        /// [`checked_mul`]: Self::checked_mul
        /// [`unwrap_unchecked`]: Option::unwrap_unchecked
        #[must_use]
        #[inline(always)]
        pub const unsafe fn unchecked_mul(self, rhs: Self) -> Self {
            match self.checked_mul(rhs) {
                Some(value) => value,
                // SAFETY: this is guaranteed to be safe by the caller.
                None => unsafe { core::hint::unreachable_unchecked() },
            }
        }

        /// Unchecked shift left. Computes `self << rhs`, assuming that
        /// `rhs` is less than the number of bits in `self`.
        ///
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        ///
        /// # Safety
        ///
        /// This results in undefined behavior if `rhs` is larger than
        /// or equal to the number of bits in `self`,
        /// i.e. when [`checked_shl`] would return `None`.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::unchecked_shl`].")]
        ///
        /// [`checked_shl`]: Self::checked_shl
        #[must_use]
        #[inline(always)]
        pub const unsafe fn unchecked_shl(self, rhs: u32) -> Self {
            match self.checked_shl(rhs) {
                Some(value) => value,
                // SAFETY: this is guaranteed to be safe by the caller.
                None => unsafe { core::hint::unreachable_unchecked() },
            }
        }

        /// Unchecked shift right. Computes `self >> rhs`, assuming that
        /// `rhs` is less than the number of bits in `self`.
        ///
        /// This is a nightly-only experimental API in the Rust core implementation,
        /// and therefore is subject to change at any time.
        ///
        /// # Safety
        ///
        /// This results in undefined behavior if `rhs` is larger than
        /// or equal to the number of bits in `self`,
        /// i.e. when [`checked_shr`] would return `None`.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::unchecked_shr`].")]
        ///
        /// [`checked_shr`]: Self::checked_shr
        #[must_use]
        #[inline(always)]
        pub const unsafe fn unchecked_shr(self, rhs: u32) -> Self {
            match self.checked_shr(rhs) {
                Some(value) => value,
                // SAFETY: this is guaranteed to be safe by the caller.
                None => unsafe { core::hint::unreachable_unchecked() },
            }
        }
    };
}

pub(crate) use define;
