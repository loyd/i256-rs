//! Arithematic operations which only return a value if no overflow occurs.

#[rustfmt::skip]
macro_rules! define {
    (type => $t:ty,wide_type => $wide_t:ty) => {
        /// Checked integer addition. Computes `self + rhs`, returning `None`
        /// if overflow occurred.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_add`].")]
        #[inline(always)]
        pub const fn checked_add(self, rhs: Self) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add(rhs);
            if !overflowed {
                Some(value)
            } else {
                None
            }
        }

        /// Checked integer subtraction. Computes `self - rhs`, returning `None`
        /// if overflow occurred.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_sub`].")]
        #[inline(always)]
        pub const fn checked_sub(self, rhs: Self) -> Option<Self> {
            let (value, overflowed) = self.overflowing_sub(rhs);
            if !overflowed {
                Some(value)
            } else {
                None
            }
        }

        /// Checked integer multiplication. Computes `self * rhs`, returning `None`
        /// if overflow occurred.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_mul`].")]
        #[inline(always)]
        pub const fn checked_mul(self, rhs: Self) -> Option<Self> {
            let (value, overflowed) = self.overflowing_mul(rhs);
            if !overflowed {
                Some(value)
            } else {
                None
            }
        }

        /// Checked exponentiation. Computes `self.pow(exp)`, returning `None`
        /// if overflow occurred.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_pow`].")]
        #[inline(always)]
        pub const fn checked_pow(self, base: u32) -> Option<Self> {
            match self.overflowing_pow(base) {
                (value, false) => Some(value),
                _ => None,
            }
        }

        /// Checked integer division. Computes `self / rhs`, returning `None`
        /// `rhs == 0` or the division results in overflow (signed only).
        ///
        /// This allows storing of both the quotient and remainder without
        /// making repeated calls.
        #[inline]
        pub fn checked_div_rem(self, n: Self) -> Option<(Self, Self)> {
            if self.is_div_none(n) {
                None
            } else {
                Some(self.wrapping_div_rem(n))
            }
        }

        /// Checked integer division. Computes `self / rhs`, returning `None`
        /// `rhs == 0` or the division results in overflow (signed only).
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_div`].")]
        #[inline(always)]
        pub fn checked_div(self, rhs: Self) -> Option<Self> {
            if self.is_div_none(rhs) {
                None
            } else {
                Some(self.wrapping_div(rhs))
            }
        }

        /// Checked integer division. Computes `self % rhs`, returning `None`
        /// `rhs == 0` or the division results in overflow (signed only).
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_rem`].")]
        #[inline(always)]
        pub fn checked_rem(self, rhs: Self) -> Option<Self> {
            if self.is_div_none(rhs) {
                None
            } else {
                Some(self.wrapping_rem(rhs))
            }
        }

        /// Checked Euclidean division. Computes `self.div_euclid(rhs)`,
        /// returning `None` if `rhs == 0` or the division results in
        /// overflow (signed only).
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_div_euclid`].")]
        #[inline(always)]
        pub fn checked_div_euclid(self, rhs: Self) -> Option<Self> {
            if self.is_div_none(rhs) {
                None
            } else {
                Some(self.wrapping_div_euclid(rhs))
            }
        }

        /// Checked Euclidean modulo. Computes `self.rem_euclid(rhs)`,
        /// returning `None` if `rhs == 0` or the division results in
        /// overflow (signed only).
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_rem_euclid`].")]
        #[inline(always)]
        pub fn checked_rem_euclid(self, rhs: Self) -> Option<Self> {
            if self.is_div_none(rhs) {
                None
            } else {
                Some(self.wrapping_rem_euclid(rhs))
            }
        }

        /// Checked shift left. Computes `self << rhs`, returning `None` if `rhs` is
        /// larger than or equal to the number of bits in `self`.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_shl`].")]
        #[inline(always)]
        pub const fn checked_shl(self, rhs: u32) -> Option<Self> {
            // Not using overflowing_shl as that's a wrapping shift
            if rhs < Self::BITS {
                Some(self.wrapping_shl(rhs))
            } else {
                None
            }
        }

        /// Checked shift right. Computes `self >> rhs`, returning `None` if `rhs`
        /// is larger than or equal to the number of bits in `self`.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_shr`].")]
        #[inline(always)]
        pub const fn checked_shr(self, rhs: u32) -> Option<Self> {
            // Not using overflowing_shr as that's a wrapping shift
            if rhs < Self::BITS {
                Some(self.wrapping_shr(rhs))
            } else {
                None
            }
        }

        /// Returns the base 2 logarithm of the number, rounded down.
        ///
        /// Returns `None` if the number is negative or zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::checked_ilog2`].")]
        #[inline]
        pub const fn checked_ilog2(self) -> Option<u32> {
            match self.le_const(Self::from_u8(0)) {
                true => None,
                false => Some(Self::BITS - 1 - self.leading_zeros()),
            }
        }
    };
}

pub(crate) use define;
