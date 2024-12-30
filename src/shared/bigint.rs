//! Big integer helpers.
//!
//! These aim to be drop-in replacements for `bigint_helper_methods`.

#[rustfmt::skip]
macro_rules! define {
    (wide_type => $wide_t:ty) => {
        /// Calculates `self` + `rhs` + `carry` and returns a tuple containing
        /// the sum and the output carry.
        ///
        /// Performs "ternary addition" of two integer operands and a carry-in
        /// bit, and returns an output integer and a carry-out bit. This allows
        /// chaining together multiple additions to create a wider addition, and
        /// can be useful for bignum addition.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($wide_t, carrying_add)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn carrying_add(self, rhs: Self, carry: bool) -> (Self, bool) {
            let (a, b) = self.overflowing_add(rhs);
            let (c, d) = a.overflowing_add_ulimb(carry as $crate::ULimb);
            (c, b | d)
        }

        /// Calculates `self` &minus; `rhs` &minus; `borrow` and returns a tuple
        /// containing the difference and the output borrow.
        ///
        /// Performs "ternary subtraction" by subtracting both an integer
        /// operand and a borrow-in bit from `self`, and returns an output
        /// integer and a borrow-out bit. This allows chaining together multiple
        /// subtractions to create a wider subtraction, and can be useful for
        /// bignum subtraction.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($wide_t, borrowing_sub)]
        #[doc = $crate::shared::docs::nightly_doc!()]
        #[inline]
        #[must_use]
        pub const fn borrowing_sub(self, rhs: Self, borrow: bool) -> (Self, bool) {
            let (a, b) = self.overflowing_sub(rhs);
            let (c, d) = a.overflowing_sub_ulimb(borrow as $crate::ULimb);
            (c, b | d)
        }
    };
}

pub(crate) use define;
