//! Operations for our limb operations on big integers.

macro_rules! define {
    () => {
        $crate::shared::limb::define!();

        // LIMB

        /// Add [`ILimb`][crate::ILimb] to the big integer.
        ///
        #[doc = $crate::shared::docs::limb_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
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

        /// Subtract [`ILimb`][crate::ILimb] from the big integer.
        ///
        #[doc = $crate::shared::docs::limb_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
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

        /// Multiply our big integer by [`ILimb`][crate::ILimb].
        ///
        #[doc = $crate::shared::docs::limb_doc!(multiplication)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
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
        /// by [`ILimb`][crate::ILimb].
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
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

        /// Get the quotient of our big integer divided by [`ILimb`][crate::ILimb].
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_ilimb(self, n: $crate::ILimb) -> Self {
            self.div_rem_ilimb(n).0
        }

        /// Get the remainder of our big integer divided by [`ILimb`][crate::ILimb].
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn rem_ilimb(self, n: $crate::ILimb) -> $crate::ILimb {
            self.div_rem_ilimb(n).1
        }

        // WIDE

        /// Add [`IWide`][crate::IWide] to the big integer.
        ///
        #[doc = $crate::shared::docs::wide_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn add_iwide(self, n: $crate::IWide) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_add_iwide(n)
            } else {
                match self.checked_add_iwide(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to add with overflow"),
                }
            }
        }

        /// Subtract [`IWide`][crate::IWide] from the big integer.
        ///
        #[doc = $crate::shared::docs::wide_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn sub_iwide(self, n: $crate::IWide) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_sub_iwide(n)
            } else {
                match self.checked_sub_iwide(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to subtract with overflow"),
                }
            }
        }

        /// Multiply our big integer by [`IWide`][crate::IWide].
        ///
        #[doc = $crate::shared::docs::wide_doc!(multiplication)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn mul_iwide(self, n: $crate::IWide) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_mul_iwide(n)
            } else {
                match self.checked_mul_iwide(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to multiply with overflow"),
                }
            }
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`IWide`][crate::IWide].
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_rem_iwide(self, n: $crate::IWide) -> (Self, $crate::IWide) {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_rem_iwide(n)
            } else {
                match self.checked_div_rem_iwide(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }

        /// Get the quotient of our big integer divided by [`IWide`][crate::IWide].
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn div_iwide(self, n: $crate::IWide) -> Self {
            self.div_rem_iwide(n).0
        }

        /// Get the remainder of our big integer divided by [`IWide`][crate::IWide].
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn rem_iwide(self, n: $crate::IWide) -> $crate::IWide {
            self.div_rem_iwide(n).1
        }

        // U32

        // TODO: Add

        // U64

        // TODO: Add

        // U128

        // TODO: Add
    };

    (@wrapping) => {
        $crate::shared::limb::define!(@wrapping);

        // LIMB

        /// Add [`ULimb`][crate::ULimb] to the big integer, wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_add_ulimb(self, n: $crate::ULimb) -> Self {
            let limbs = $crate::math::add::wrapping_ulimb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Add [`ILimb`][crate::ILimb] to the big integer, wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_add_ilimb(self, n: $crate::ILimb) -> Self {
            let limbs = $crate::math::add::wrapping_ilimb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Subtract [`ULimb`][crate::ULimb] from the big integer, wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_sub_ulimb(self, n: $crate::ULimb) -> Self {
            let limbs = $crate::math::sub::wrapping_ulimb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Subtract [`ILimb`][crate::ILimb] from the big integer, wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_sub_ilimb(self, n: $crate::ILimb) -> Self {
            let limbs = $crate::math::sub::wrapping_ilimb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Multiply our big integer by [`ULimb`][crate::ULimb], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(multiplication)]
        /// This in worst case 5 `mul`, 3 `add`, and 6 `sub` instructions,
        /// because of branching in nearly every case, it has better
        /// performance and optimizes nicely for small multiplications.
        /// See [`u256::wrapping_mul_ulimb`] for a more detailed analysis,
        /// which is identical.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_mul_ulimb(self, n: $crate::ULimb) -> Self {
            let limbs = $crate::math::mul::wrapping_ulimb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Multiply our big integer by [`ILimb`][crate::ILimb], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(multiplication)]
        /// This in worst case 4 `mul`, 3 `add`, and 6 `sub` instructions,
        /// because of branching in nearly every case, it has better
        /// performance and optimizes nicely for small multiplications.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_mul_ilimb(self, n: $crate::ILimb) -> Self {
            let limbs = $crate::math::mul::wrapping_ilimb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`ULimb`][crate::ULimb], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        /// This always wraps, which can never happen in practice. This
        /// has to use the floor division since we can never have a non-
        /// negative rem.
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
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
        /// by [`ILimb`][crate::ILimb], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        /// This always wraps, which can never happen in practice.
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
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
        /// by [`ILimb`][crate::ILimb], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_ilimb(self, n: $crate::ILimb) -> Self {
            self.wrapping_div_rem_ilimb(n).0
        }

        /// Get the remainder of our big integer divided
        /// by [`ILimb`][crate::ILimb], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_rem_ilimb(self, n: $crate::ILimb) -> $crate::ILimb {
            self.wrapping_div_rem_ilimb(n).1
        }

        // WIDE

        /// Add [`UWide`][crate::UWide] to the big integer, wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_add_uwide(self, n: $crate::UWide) -> Self {
            todo!();
            //let limbs = $crate::math::add::wrapping_uwide(&self.to_ne_limbs(), n);
            //Self::from_ne_limbs(limbs)
        }

        /// Add [`IWide`][crate::IWide] to the big integer, wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_add_iwide(self, n: $crate::IWide) -> Self {
            todo!();
            //let limbs = $crate::math::add::wrapping_iwide(&self.to_ne_limbs(), n);
            //Self::from_ne_limbs(limbs)
        }

        /// Subtract [`UWide`][crate::UWide] from the big integer, wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_sub_uwide(self, n: $crate::UWide) -> Self {
            todo!();
            //let limbs = $crate::math::sub::wrapping_uwide(&self.to_ne_limbs(), n);
            //Self::from_ne_limbs(limbs)
        }

        /// Subtract [`IWide`][crate::IWide] from the big integer, wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_sub_iwide(self, n: $crate::IWide) -> Self {
            todo!();
            //let limbs = $crate::math::sub::wrapping_iwide(&self.to_ne_limbs(), n);
            //Self::from_ne_limbs(limbs)
        }

        /// Multiply our big integer by [`UWide`][crate::UWide], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(multiplication)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_mul_uwide(self, n: $crate::UWide) -> Self {
            let limbs = $crate::math::mul::wrapping_uwide(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Multiply our big integer by [`IWide`][crate::IWide], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(multiplication)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_mul_iwide(self, n: $crate::IWide) -> Self {
            let limbs = $crate::math::mul::wrapping_iwide(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`UWide`][crate::UWide], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        /// This always wraps, which can never happen in practice. This
        /// has to use the floor division since we can never have a non-
        /// negative rem.
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_rem_uwide(self, n: $crate::UWide) -> (Self, $crate::UWide) {
            todo!();
//            let x = self.unsigned_abs().to_le_limbs();
//            let (div, mut rem) = $crate::math::div::limb(&x, n);
//            let mut div = Self::from_le_limbs(div);
//            if self.is_negative() {
//                div = div.wrapping_neg();
//            }
//            if self.is_negative() && rem != 0 {
//                div -= Self::from_u8(1);
//                rem = n - rem;
//            }
//            (div, rem)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`IWide`][crate::IWide], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        /// This always wraps, which can never happen in practice.
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_rem_iwide(self, n: $crate::IWide) -> (Self, $crate::IWide) {
            todo!();
//            let x = self.unsigned_abs().to_le_limbs();
//            let (div, rem) = $crate::math::div::limb(&x, n.unsigned_abs());
//            let mut div = Self::from_le_limbs(div);
//            let mut rem = rem as $crate::IWide;
//
//            if self.is_negative() != n.is_negative() {
//                div = div.wrapping_neg();
//            }
//            if self.is_negative() {
//                rem = rem.wrapping_neg();
//            }
//
//            (div, rem)
        }

        /// Get the quotient of our big integer divided
        /// by [`IWide`][crate::IWide], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_iwide(self, n: $crate::IWide) -> Self {
            self.wrapping_div_rem_iwide(n).0
        }

        /// Get the remainder of our big integer divided
        /// by [`IWide`][crate::IWide], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_rem_iwide(self, n: $crate::IWide) -> $crate::IWide {
            self.wrapping_div_rem_iwide(n).1
        }

        // U32

        // TODO: Add

        // U64

        // TODO: Add

        // U128

        // TODO: Add
    };

    (@overflowing) => {
        $crate::shared::limb::define!(@overflowing);

        // LIMB

        /// Add [`ULimb`][crate::ULimb] to the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_add_ulimb(self, n: $crate::ULimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::add::overflowing_ulimb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Add [`ILimb`][crate::ILimb] to the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_add_ilimb(self, n: $crate::ILimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::add::overflowing_ilimb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Subtract [`ULimb`][crate::ULimb] from the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_sub_ulimb(self, n: $crate::ULimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::sub::overflowing_ulimb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Subtract [`ILimb`][crate::ILimb] from the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_sub_ilimb(self, n: $crate::ILimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::sub::overflowing_ilimb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Multiply our big integer by [`ULimb`][crate::ULimb], returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(multiplication)]
        /// This in worst case 4 `mul`, 4 `add`, and 6 `sub` instructions,
        /// significantly slower than the wrapping variant.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_mul_ulimb(self, n: $crate::ULimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::mul::overflowing_ulimb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Multiply our big integer by [`ILimb`][crate::ILimb], returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(multiplication)]
        /// This in worst case 5 `mul`, 5 `add`, and 6 `sub` instructions,
        /// significantly slower than the wrapping variant.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_mul_ilimb(self, n: $crate::ILimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::mul::overflowing_ilimb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`ILimb`][crate::ILimb], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_div_rem_ilimb(self, n: $crate::ILimb) -> ((Self, $crate::ILimb), bool) {
            if self.eq_const(Self::MIN) && n == -1 {
                ((Self::MIN, 0), true)
            } else {
                (self.wrapping_div_rem_ilimb(n), false)
            }
        }

        /// Get the quotient of our big integer divided
        /// by [`ILimb`][crate::ILimb], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_div_ilimb(self, n: $crate::ILimb) -> (Self, bool) {
            let (value, overflowed) = self.overflowing_div_rem_ilimb(n);
            (value.0, overflowed)
        }

        /// Get the remainder of our big integer divided
        /// by [`ILimb`][crate::ILimb], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_rem_ilimb(self, n: $crate::ILimb) -> ($crate::ILimb, bool) {
            let (value, overflowed) = self.overflowing_div_rem_ilimb(n);
            (value.1, overflowed)
        }

        // WIDE

        /// Add [`UWide`][crate::UWide] to the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_add_uwide(self, n: $crate::UWide) -> (Self, bool) {
            todo!();
            //let (limbs, overflowed) = $crate::math::add::overflowing_uwide(&self.to_ne_limbs(), n);
            //(Self::from_ne_limbs(limbs), overflowed)
        }

        /// Add [`IWide`][crate::IWide] to the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_add_iwide(self, n: $crate::IWide) -> (Self, bool) {
            todo!();
            //let (limbs, overflowed) = $crate::math::add::overflowing_iwide(&self.to_ne_limbs(), n);
            //(Self::from_ne_limbs(limbs), overflowed)
        }

        /// Subtract [`UWide`][crate::UWide] from the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_sub_uwide(self, n: $crate::UWide) -> (Self, bool) {
            todo!();
            //let (limbs, overflowed) = $crate::math::sub::overflowing_uwide(&self.to_ne_limbs(), n);
            //(Self::from_ne_limbs(limbs), overflowed)
        }

        /// Subtract [`IWide`][crate::IWide] from the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_sub_iwide(self, n: $crate::IWide) -> (Self, bool) {
            todo!();
            //let (limbs, overflowed) = $crate::math::sub::overflowing_iwide(&self.to_ne_limbs(), n);
            //(Self::from_ne_limbs(limbs), overflowed)
        }

        /// Multiply our big integer by [`UWide`][crate::UWide], returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(multiplication)]
        /// This in worst case 4 `mul`, 4 `add`, and 6 `sub` instructions,
        /// significantly slower than the wrapping variant.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_mul_uwide(self, n: $crate::UWide) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::mul::overflowing_uwide(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Multiply our big integer by [`IWide`][crate::IWide], returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(multiplication)]
        /// This in worst case 5 `mul`, 5 `add`, and 6 `sub` instructions,
        /// significantly slower than the wrapping variant.
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_mul_iwide(self, n: $crate::IWide) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::mul::overflowing_iwide(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`IWide`][crate::IWide], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_div_rem_iwide(self, n: $crate::IWide) -> ((Self, $crate::IWide), bool) {
            if self.eq_const(Self::MIN) && n == -1 {
                ((Self::MIN, 0), true)
            } else {
                (self.wrapping_div_rem_iwide(n), false)
            }
        }

        /// Get the quotient of our big integer divided
        /// by [`IWide`][crate::IWide], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_div_iwide(self, n: $crate::IWide) -> (Self, bool) {
            let (value, overflowed) = self.overflowing_div_rem_iwide(n);
            (value.0, overflowed)
        }

        /// Get the remainder of our big integer divided
        /// by [`IWide`][crate::IWide], returning the value and if overflow
        /// occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn overflowing_rem_iwide(self, n: $crate::IWide) -> ($crate::IWide, bool) {
            let (value, overflowed) = self.overflowing_div_rem_iwide(n);
            (value.1, overflowed)
        }

        // U32

        // TODO: Add

        // U64

        // TODO: Add

        // U128

        // TODO: Add
    };

    (@checked) => {
        $crate::shared::limb::define!(@checked);

        // LIMB

        /// Add [`ILimb`][crate::ILimb] to the big integer, returning None on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_add_ilimb(self, n: $crate::ILimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add_ilimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Subtract [`ILimb`][crate::ILimb] from the big integer, returning None on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_sub_ilimb(self, n: $crate::ILimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_sub_ilimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Multiply our big integer by [`ILimb`][crate::ILimb], returning None on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(multiplication)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_mul_ilimb(self, n: $crate::ILimb) -> Option<Self> {
            let (value, overflowed) = self.overflowing_mul_ilimb(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`ILimb`][crate::ILimb], returning None on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
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
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_div_ilimb(self, n: $crate::ILimb) -> Option<Self> {
            Some(self.checked_div_rem_ilimb(n)?.0)
        }

        /// Get the remainder of our big integer divided by a signed
        /// limb, returning None on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_rem_ilimb(self, n: $crate::ILimb) -> Option<$crate::ILimb> {
            Some(self.checked_div_rem_ilimb(n)?.1)
        }

        // WIDE

        /// Add [`IWide`][crate::IWide] to the big integer, returning None on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_add_iwide(self, n: $crate::IWide) -> Option<Self> {
            let (value, overflowed) = self.overflowing_add_iwide(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Subtract [`IWide`][crate::IWide] from the big integer, returning None on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_sub_iwide(self, n: $crate::IWide) -> Option<Self> {
            let (value, overflowed) = self.overflowing_sub_iwide(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Multiply our big integer by [`IWide`][crate::IWide], returning None on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(multiplication)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn checked_mul_iwide(self, n: $crate::IWide) -> Option<Self> {
            let (value, overflowed) = self.overflowing_mul_iwide(n);
            if overflowed {
                None
            } else {
                Some(value)
            }
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`IWide`][crate::IWide], returning None on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_div_rem_iwide(self, n: $crate::IWide) -> Option<(Self, $crate::IWide)> {
            if n == 0 {
                None
            } else {
                Some(self.wrapping_div_rem_iwide(n))
            }
        }

        /// Get the quotient of our big integer divided by a signed
        /// limb, returning None on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_div_iwide(self, n: $crate::IWide) -> Option<Self> {
            Some(self.checked_div_rem_iwide(n)?.0)
        }

        /// Get the remainder of our big integer divided by a signed
        /// limb, returning None on overflow or division by 0.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn checked_rem_iwide(self, n: $crate::IWide) -> Option<$crate::IWide> {
            Some(self.checked_div_rem_iwide(n)?.1)
        }

        // U32

        // TODO: Add

        // U64

        // TODO: Add

        // U128

        // TODO: Add
    };

    (@all) => {
        $crate::int::limb::define!();
        $crate::int::limb::define!(@wrapping);
        $crate::int::limb::define!(@overflowing);
        $crate::int::limb::define!(@checked);
    };
}

pub(crate) use define;
