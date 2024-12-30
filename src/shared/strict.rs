//! Strict arithemetic operations, which always panic on overflow.

#[rustfmt::skip]
macro_rules! define {
    (type => $t:ty,wide_type => $wide_t:ty) => {
        /// Strict integer addition. Computes `self + rhs`, panicking
        /// if overflow occurred.
        ///
        #[doc = $crate::shared::docs::strict_doc!(panics)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($wide_t, strict_add)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn strict_add(self, rhs: Self) -> Self {
            match self.checked_add(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to add with overflow"),
            }
        }

        /// Strict integer subtraction. Computes `self - rhs`, panicking if
        /// overflow occurred.
        ///
        #[doc = $crate::shared::docs::strict_doc!(panics)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($wide_t, strict_sub)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn strict_sub(self, rhs: Self) -> Self {
            match self.checked_sub(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to subtract with overflow"),
            }
        }

        /// Strict integer multiplication. Computes `self * rhs`, panicking if
        /// overflow occurred.
        ///
        #[doc = $crate::shared::docs::strict_doc!(panics)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($wide_t, strict_mul)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn strict_mul(self, rhs: Self) -> Self {
            match self.checked_mul(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to subtract with overflow"),
            }
        }

        /// Strict exponentiation. Computes `self.pow(exp)`, panicking if
        /// overflow occurred.
        ///
        #[doc = $crate::shared::docs::strict_doc!(panics)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($wide_t, strict_pow)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn strict_pow(self, rhs: u32) -> Self {
            match self.checked_pow(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to multiply with overflow"),
            }
        }

        /// Strict shift left. Computes `self << rhs`, panicking if `rhs` is larger
        /// than or equal to the number of bits in `self`.
        ///
        #[doc = $crate::shared::docs::strict_doc!(panics)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($wide_t, strict_shl)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn strict_shl(self, rhs: u32) -> Self {
            match self.checked_shl(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to shift left with overflow"),
            }
        }

        /// Strict shift right. Computes `self >> rhs`, panicking `rhs` is
        /// larger than or equal to the number of bits in `self`.
        ///
        #[doc = $crate::shared::docs::strict_doc!(panics)]
        ///
        #[doc = $crate::shared::docs::primitive_doc!($wide_t, strict_shr)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn strict_shr(self, rhs: u32) -> Self {
            match self.checked_shr(rhs) {
                Some(v) => v,
                None => core::panic!("attempt to shift right with overflow"),
            }
        }
    };
}

pub(crate) use define;
