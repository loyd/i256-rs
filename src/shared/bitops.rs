//! Bitwise operations for our types.

/// Defines some of the bitwise operator definitions.
///
/// See the bench on `bit_algos` for some of the choices.
#[rustfmt::skip]
macro_rules! define {
    (
        type => $t:ty,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        /// Returns the number of ones in the binary representation of `self`.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, count_ones)]
        #[inline(always)]
        pub const fn count_ones(self) -> u32 {
            // NOTE: Rust vectorizes this nicely on x86_64.
            let mut count = 0;
            let mut i = 0;
            while i < Self::LIMBS {
                count += self.limbs[i].count_ones();
                i += 1;
            }
            count
        }

        /// Returns the number of zeros in the binary representation of `self`.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, count_zeros)]
        #[inline(always)]
        pub const fn count_zeros(self) -> u32 {
            self.not_const().count_ones()
        }

        /// Returns the number of leading zeros in the binary representation of
        /// `self`.
        ///
        /// Depending on what you're doing with the value, you might also be
        /// interested in the `ilog2` function which returns a consistent
        /// number, even if the type widens.
        ///
        /// # Examples
        ///
        /// ```rust
        /// # use i256::i256;
        /// let n = i256::MAX >> 2i32;
        /// assert_eq!(n.leading_zeros(), 3);
        ///
        /// let min = i256::MIN;
        /// assert_eq!(min.leading_zeros(), 0);
        ///
        /// let zero = i256::from_u8(0);
        /// assert_eq!(zero.leading_zeros(), 256);
        ///
        /// let max = i256::MAX;
        /// assert_eq!(max.leading_zeros(), 1);
        /// ```
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, leading_zeros)]
        #[inline]
        pub const fn leading_zeros(self) -> u32 {
            let mut count = 0;
            let mut i = 0;
            while i < Self::LIMBS && count == i as u32 * $crate::ULimb::BITS {
                count += self.get_limb(Self::LIMBS - i - 1).leading_zeros();
                i += 1;
            }
            count
        }

        /// Returns the number of trailing zeros in the binary representation of
        /// `self`.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, trailing_zeros)]
        #[inline]
        pub const fn trailing_zeros(self) -> u32 {
            let mut count = 0;
            let mut i = 0;
            while i < Self::LIMBS && count == i as u32 * $crate::ULimb::BITS {
                count += self.get_limb(i).trailing_zeros();
                i += 1;
            }
            count
        }

        /// Returns the number of leading ones in the binary representation of
        /// `self`.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, leading_ones)]
        #[inline(always)]
        pub const fn leading_ones(self) -> u32 {
            self.not_const().leading_zeros()
        }

        /// Returns the number of trailing ones in the binary representation of
        /// `self`.
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, trailing_ones)]
        #[inline(always)]
        pub const fn trailing_ones(self) -> u32 {
            self.not_const().trailing_zeros()
        }

        // NOTE: These optimize super well, and flatten out entirely.

        /// Const implementation of `BitAnd`.
        #[inline(always)]
        pub const fn bitand_const(self, rhs: Self) -> Self {
            let lhs_limbs = self.to_ne_limbs();
            let rhs_limbs = rhs.to_ne_limbs();
            let mut result = [0; Self::LIMBS];
            let mut i = 0;
            while i < Self::LIMBS {
                result[i] = lhs_limbs[i] & rhs_limbs[i];
                i += 1;
            }
            Self::from_ne_limbs(result)
        }

        /// Const implementation of `BitOr`.
        #[inline(always)]
        pub const fn bitor_const(self, rhs: Self) -> Self {
            let lhs_limbs = self.to_ne_limbs();
            let rhs_limbs = rhs.to_ne_limbs();
            let mut result = [0; Self::LIMBS];
            let mut i = 0;
            while i < Self::LIMBS {
                result[i] = lhs_limbs[i] | rhs_limbs[i];
                i += 1;
            }
            Self::from_ne_limbs(result)
        }

        /// Const implementation of `BitXor`.
        #[inline(always)]
        pub const fn bitxor_const(self, rhs: Self) -> Self {
            let lhs_limbs = self.to_ne_limbs();
            let rhs_limbs = rhs.to_ne_limbs();
            let mut result = [0; Self::LIMBS];
            let mut i = 0;
            while i < Self::LIMBS {
                result[i] = lhs_limbs[i] ^ rhs_limbs[i];
                i += 1;
            }
            Self::from_ne_limbs(result)
        }

        /// Const implementation of `Not`.
        #[inline(always)]
        pub const fn not_const(self) -> Self {
            let limbs = self.to_ne_limbs();
            let mut result = [0; Self::LIMBS];
            let mut i = 0;
            while i < Self::LIMBS {
                result[i] = !limbs[i];
                i += 1;
            }
            Self::from_ne_limbs(result)
        }

        /// Shifts the bits to the left by a specified amount, `n`,
        /// wrapping the truncated bits to the end of the resulting integer.
        ///
        /// Please note this isn't the same operation as the `<<` shifting operator!
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, rotate_left)]
        #[inline(always)]
        pub const fn rotate_left(self, n: u32) -> Self {
            let result = $crate::math::rotate::left_wide(self.to_ne_wide(), n);
            Self::from_ne_wide(result)
        }

        /// Shifts the bits to the right by a specified amount, `n`,
        /// wrapping the truncated bits to the beginning of the resulting
        /// integer.
        ///
        /// Please note this isn't the same operation as the `>>` shifting operator!
        ///
        #[doc = $crate::shared::docs::primitive_doc!($see_t, rotate_right)]
        #[inline(always)]
        pub const fn rotate_right(self, n: u32) -> Self {
            let result = $crate::math::rotate::right_wide(self.to_ne_wide(), n);
            Self::from_ne_wide(result)
        }
    };
}

pub(crate) use define;

#[rustfmt::skip]
macro_rules! wrapping_shl_doc {
    ($wide_t:ty) => {
        concat!(
"
Panic-free bitwise shift-left; yields `self << mask(rhs)`,
where `mask` removes any high-order bits of `rhs` that
would cause the shift to exceed the bitwidth of the type.

Note that this is *not* the same as a rotate-left; the
RHS of a wrapping shift-left is restricted to the range
of the type, rather than the bits shifted out of the LHS
being returned to the other end. The primitive integer
types all implement a [`rotate_left`](Self::rotate_left) function,
which may be what you want instead.

See [`", stringify!($wide_t), "::wrapping_shl`].
"
        )
    };
}

pub(crate) use wrapping_shl_doc;

#[rustfmt::skip]
macro_rules! wrapping_shr_doc {
    ($wide_t:ty) => {
        concat!(
"
Panic-free bitwise shift-right; yields `self >> mask(rhs)`,
where `mask` removes any high-order bits of `rhs` that
would cause the shift to exceed the bitwidth of the type.

Note that this is *not* the same as a rotate-right; the
RHS of a wrapping shift-right is restricted to the range
of the type, rather than the bits shifted out of the LHS
being returned to the other end. The primitive integer
types all implement a [`rotate_right`](Self::rotate_right) function,
which may be what you want instead.

See [`", stringify!($wide_t), "::wrapping_shr`].
"
        )
    };
}

pub(crate) use wrapping_shr_doc;

macro_rules! traits {
    ($t:ty) => {
        impl core::ops::BitAnd for $t {
            type Output = Self;

            #[inline(always)]
            fn bitand(self, rhs: Self) -> Self::Output {
                self.bitand_const(rhs)
            }
        }
        impl core::ops::BitOr for $t {
            type Output = $t;

            #[inline(always)]
            fn bitor(self, rhs: Self) -> Self::Output {
                self.bitor_const(rhs)
            }
        }

        impl core::ops::BitXor for $t {
            type Output = Self;

            #[inline(always)]
            fn bitxor(self, rhs: Self) -> Self::Output {
                self.bitxor_const(rhs)
            }
        }

        $crate::shared::traits::define! {
            type => $t, impl => core::ops::BitAnd, op => bitand, assign => core::ops::BitAndAssign, assign_op => bitand_assign,
            type => $t, impl => core::ops::BitOr, op => bitor, assign => core::ops::BitOrAssign, assign_op => bitor_assign,
            type => $t, impl => core::ops::BitXor, op => bitxor, assign => core::ops::BitXorAssign, assign_op => bitxor_assign,
        }
    };
}

pub(crate) use traits;
