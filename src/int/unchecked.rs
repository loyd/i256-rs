//! Unchecked arithmetic operations.
//!
//! On overflow or other unexpected cases, this results in
//! undefined behavior.

#[rustfmt::skip]
macro_rules! define {
    (unsigned_type => $u_t:ty) => {
        $crate::shared::unchecked::define!(type => $u_t, wide_type => i128);

        /// Unchecked negation. Computes `-self`, assuming overflow cannot occur.
        ///
        #[doc = $crate::shared::docs::unchecked_doc!()]
        ///
        #[doc = $crate::shared::docs::primitive_doc!(i128, unchecked_neg)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub unsafe fn unchecked_neg(self) -> Self {
            match self.checked_neg() {
                Some(value) => value,
                // SAFETY: this is guaranteed to be safe by the caller.
                None => unsafe { core::hint::unreachable_unchecked() },
            }
        }
    }
}

pub(crate) use define;
