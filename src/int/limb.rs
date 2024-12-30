//! Operations for our limb operations on big integers.

macro_rules! define {
    () => {
        $crate::shared::limb::define!();

        /// Add a signed limb to the big integer.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn add_ilimb(self, n: $crate::ILimb) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_add_ilimb(n)
            } else {
                match self.checked_add_ilimb(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to add with overflow"),
                }
            }
        }

        /// Subtract a signed limb from the big integer.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn sub_ilimb(self, n: $crate::ILimb) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_sub_ilimb(n)
            } else {
                match self.checked_sub_ilimb(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to subtract with overflow"),
                }
            }
        }

        /// Multiply our big integer by a signed limb.
        ///
        /// This allows optimizations a full multiplication cannot do.
        #[inline(always)]
        pub const fn mul_ilimb(self, n: $crate::ILimb) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_mul_ilimb(n)
            } else {
                match self.checked_mul_ilimb(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to multiply with overflow"),
                }
            }
        }

        /// Get the quotient and remainder of our big integer divided
        /// by a signed limb.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline]
        pub fn div_rem_ilimb(self, n: $crate::ILimb) -> (Self, $crate::ILimb) {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_rem_ilimb(n)
            } else {
                match self.checked_div_rem_ilimb(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Get the quotient of our big integer divided by a signed limb.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn div_ilimb(self, n: $crate::ILimb) -> Self {
            self.div_rem_ilimb(n).0
        }

        /// Get the remainder of our big integer divided by a signed limb.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn rem_ilimb(self, n: $crate::ILimb) -> $crate::ILimb {
            self.div_rem_ilimb(n).1
        }
    };

    (@wrapping) => {
        $crate::shared::limb::define!(@wrapping);

        /// Add an unsigned limb to the big integer, wrapping on overflow.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn wrapping_add_ulimb(self, n: $crate::ULimb) -> Self {
            let limbs = $crate::math::add::wrapping_ulimb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Add a signed limb to the big integer, wrapping on overflow.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn wrapping_add_ilimb(self, n: $crate::ILimb) -> Self {
            let limbs = $crate::math::add::wrapping_ilimb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Subtract an unsigned limb from the big integer, wrapping on
        /// overflow.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn wrapping_sub_ulimb(self, n: $crate::ULimb) -> Self {
            let limbs = $crate::math::sub::wrapping_ulimb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Subtract a signed limb from the big integer, wrapping on
        /// overflow.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn wrapping_sub_ilimb(self, n: $crate::ILimb) -> Self {
            let limbs = $crate::math::sub::wrapping_ilimb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Multiply our big integer by an unsigned limb, wrapping on overflow.
        ///
        /// This allows optimizations a full multiplication cannot do.
        /// This in worst case 5 `mul`, 3 `add`, and 6 `sub` instructions,
        /// because of branching in nearly every case, it has better
        /// performance and optimizes nicely for small multiplications.
        /// See [`u256::wrapping_mul_ulimb`] for a more detailed analysis,
        /// which is identical.
        #[inline(always)]
        pub const fn wrapping_mul_ulimb(self, n: $crate::ULimb) -> Self {
            let limbs = $crate::math::mul::wrapping_ulimb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Multiply our big integer by a signed limb, wrapping on overflow.
        ///
        /// This allows optimizations a full multiplication cannot do.
        /// This in worst case 4 `mul`, 3 `add`, and 6 `sub` instructions,
        /// because of branching in nearly every case, it has better
        /// performance and optimizes nicely for small multiplications.
        #[inline(always)]
        pub const fn wrapping_mul_ilimb(self, n: $crate::ILimb) -> Self {
            let limbs = $crate::math::mul::wrapping_ilimb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by an unsigned limb, wrapping on overflow.
        ///
        /// This allows optimizations a full division cannot do. This always
        /// wraps, which can never happen in practice. This has to use
        /// the floor division since we can never have a non-negative rem.
        #[inline]
        pub fn wrapping_div_rem_ulimb(self, n: $crate::ULimb) -> (Self, $crate::ULimb) {
            let x = self.unsigned_abs().to_le_limbs();
            let (div, mut rem) = $crate::math::div::limb(&x, n);
            let mut div = Self::from_le_limbs(div);
            if self.is_negative() {
                div = div.wrapping_neg();
            }
            // rem is always positive: `-65 % 64` is 63
            // however, if we're negative and have a remainder,
            // we need to adjust since the remainder assumes the
            // floor of a positive value
            if self.is_negative() && rem != 0 {
                div -= Self::from_u8(1);
                rem = n - rem;
            }
            (div, rem)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by a signed limb, wrapping on overflow.
        ///
        /// This allows optimizations a full division cannot do. This always
        /// wraps, which can never happen in practice.
        #[inline]
        pub fn wrapping_div_rem_ilimb(self, n: $crate::ILimb) -> (Self, $crate::ILimb) {
            let x = self.unsigned_abs().to_le_limbs();
            let (div, rem) = $crate::math::div::limb(&x, n.unsigned_abs());
            let mut div = Self::from_le_limbs(div);
            let mut rem = rem as $crate::ILimb;

            // convert to our correct signs, get the product
            // NOTE: Rust has different behavior than languages like
            // Python, where `-1 % 2 == 1` and `-1 % -2 == -1`. In
            // Rust, both are `-1`.
            if self.is_negative() != n.is_negative() {
                div = div.wrapping_neg();
            }
            if self.is_negative() {
                rem = rem.wrapping_neg();
            }

            (div, rem)
        }

        /// Get the quotient of our big integer divided
        /// by a signed limb, wrapping on overflow.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn wrapping_div_ilimb(self, n: $crate::ILimb) -> Self {
            self.wrapping_div_rem_ilimb(n).0
        }

        /// Get the remainder of our big integer divided
        /// by a signed limb, wrapping on overflow.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn wrapping_rem_ilimb(self, n: $crate::ILimb) -> $crate::ILimb {
            self.wrapping_div_rem_ilimb(n).1
        }
    };

    (@overflowing) => {
        $crate::shared::limb::define!(@overflowing);

        /// Add an unsigned limb to the big integer, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn overflowing_add_ulimb(self, n: $crate::ULimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::add::overflowing_ulimb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Add a signed limb to the big integer, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn overflowing_add_ilimb(self, n: $crate::ILimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::add::overflowing_ilimb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Subtract an unsigned limb from the big integer, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn overflowing_sub_ulimb(self, n: $crate::ULimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::sub::overflowing_ulimb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Subtract a signed limb from the big integer, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn overflowing_sub_ilimb(self, n: $crate::ILimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::sub::overflowing_ilimb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Multiply our big integer by an unsigned limb, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full multiplication cannot do.
        /// This in worst case 4 `mul`, 4 `add`, and 6 `sub` instructions,
        /// significantly slower than the wrapping variant.
        #[inline(always)]
        pub const fn overflowing_mul_ulimb(self, n: $crate::ULimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::mul::overflowing_ulimb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Multiply our big integer by a signed limb, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full multiplication cannot do.
        /// This in worst case 5 `mul`, 5 `add`, and 6 `sub` instructions,
        /// significantly slower than the wrapping variant.
        #[inline(always)]
        pub const fn overflowing_mul_ilimb(self, n: $crate::ILimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::mul::overflowing_ilimb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by a signed limb, returning the value and if overflow
        /// occurred.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline]
        pub fn overflowing_div_rem_ilimb(self, n: $crate::ILimb) -> ((Self, $crate::ILimb), bool) {
            if self.eq_const(Self::MIN) && n == -1 {
                ((Self::MIN, 0), true)
            } else {
                (self.wrapping_div_rem_ilimb(n), false)
            }
        }

        /// Get the quotient of our big integer divided
        /// by a signed limb, returning the value and if overflow
        /// occurred.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn overflowing_div_ilimb(self, n: $crate::ILimb) -> (Self, bool) {
            let (value, overflowed) = self.overflowing_div_rem_ilimb(n);
            (value.0, overflowed)
        }

        /// Get the remainder of our big integer divided
        /// by a signed limb, returning the value and if overflow
        /// occurred.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn overflowing_rem_ilimb(self, n: $crate::ILimb) -> ($crate::ILimb, bool) {
            let (value, overflowed) = self.overflowing_div_rem_ilimb(n);
            (value.1, overflowed)
        }
    };

    (@checked) => {
        $crate::shared::limb::define!(@checked);

        /// Add a signed limb to the big integer, returning None on overflow.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn checked_add_ilimb(self, n: $crate::ILimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add_ilimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Subtract a signed limb from the big integer, returning None on overflow.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn checked_sub_ilimb(self, n: $crate::ILimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_sub_ilimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Multiply our big integer by a signed limb, returning None on overflow.
        ///
        /// This allows optimizations a full multiplication cannot do.
        #[inline(always)]
        pub const fn checked_mul_ilimb(self, n: $crate::ILimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_mul_ilimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Get the quotient and remainder of our big integer divided
        /// by a signed limb, returning None on overflow or division by 0.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline]
        pub fn checked_div_rem_ilimb(self, n: $crate::ILimb) -> Option<(Self, $crate::ILimb)> {
            if n == 0 {
                None
            } else {
                Some(self.wrapping_div_rem_ilimb(n))
            }
        }

        /// Get the quotient of our big integer divided by a signed
        /// limb, returning None on overflow or division by 0.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn checked_div_ilimb(self, n: $crate::ILimb) -> Option<Self> {
            Some(self.checked_div_rem_ilimb(n)?.0)
        }

        /// Get the remainder of our big integer divided by a signed
        /// limb, returning None on overflow or division by 0.
        ///
        /// This allows optimizations a full division cannot do.
        #[inline(always)]
        pub fn checked_rem_ilimb(self, n: $crate::ILimb) -> Option<$crate::ILimb> {
            Some(self.checked_div_rem_ilimb(n)?.1)
        }
    };

    (@all) => {
        $crate::int::limb::define!();
        $crate::int::limb::define!(@wrapping);
        $crate::int::limb::define!(@overflowing);
        $crate::int::limb::define!(@checked);
    };
}

pub(crate) use define;
