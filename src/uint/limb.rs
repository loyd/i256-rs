//! Operations for our limb operations on big integers.

macro_rules! define {
    () => {
        $crate::shared::limb::define!();
    };

    (@wrapping) => {
        $crate::shared::limb::define!(@wrapping);

        // LIMB

        /// Add [`ULimb`][crate::ULimb] to the big integer, wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_add_ulimb(self, n: $crate::ULimb) -> Self {
            let limbs = $crate::math::add::wrapping_limb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Subtract [`ULimb`][crate::ULimb] from the big integer, wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_sub_ulimb(self, n: $crate::ULimb) -> Self {
            let limbs = $crate::math::sub::wrapping_limb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Multiply our big integer by [`ULimb`][crate::ULimb], wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(multiplication)]
        ///
        /// Many different algorithms were attempted, with a soft [`mulx`] approach
        /// (1), a flat, fixed-width long multiplication (2), and a
        /// short-circuiting long multiplication (3). Algorithm (3) had the best
        /// performance for 128-bit multiplication, however, algorithm (1) was
        /// better for smaller type sizes.
        ///
        /// This also optimized much better when multiplying by a single or a
        /// half-sized item: rather than using 4 limbs, if we're multiplying
        /// `(u128, u128) * u128`, we can use 2 limbs for the right operand, and
        /// for `(u128, u128) * u64`, only 1 limb.
        ///
        /// Using algorithm (3), the addition of `(u128, u128) + (u128, u128)` is in
        /// the worst case 10 `mul` and 13 `add` instructions, while `(u128,
        /// u128) + u64` is always 4 `mul` and 3 `add` instructions without any
        /// branching. This is extremely efficient.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_mul_ulimb(self, n: $crate::ULimb) -> Self {
            // 256-Bit
            // -------
            // wrapping_mul:
            //      push    rbx
            //      mov     rcx, rdx
            //      mov     rax, rdx
            //      mul     qword ptr [rsi + 16]
            //      mov     r8, rax
            //      mov     r9, rdx
            //      mov     rax, rcx
            //      mul     qword ptr [rsi + 8]
            //      mov     r10, rax
            //      mov     r11, rdx
            //      mov     rbx, qword ptr [rsi + 24]
            //      imul    rbx, rcx
            //      mov     rax, rcx
            //      mul     qword ptr [rsi]
            //      add     rdx, r10
            //      adc     r11, r8
            //      adc     r9, rbx
            //      mov     qword ptr [rdi], rax
            //      mov     qword ptr [rdi + 8], rdx
            //      mov     qword ptr [rdi + 16], r11
            //      mov     qword ptr [rdi + 24], r9
            //      mov     rax, rdi
            //      pop     rbx
            //      ret
            let limbs = $crate::math::mul::wrapping_limb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`ULimb`][crate::ULimb], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!(n)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_rem_ulimb(self, n: $crate::ULimb) -> (Self, $crate::ULimb) {
            let (div, rem) = $crate::math::div::limb(&self.to_le_limbs(), n);
            let div = Self::from_le_limbs(div);
            (div, rem)
        }

        // WIDE

        /// Add [`UWide`][crate::UWide] to the big integer, wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_add_uwide(self, n: $crate::UWide) -> Self {
            let limbs = $crate::math::add::wrapping_wide(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Subtract [`UWide`][crate::UWide] from the big integer, wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_sub_uwide(self, n: $crate::UWide) -> Self {
            let limbs = $crate::math::sub::wrapping_wide(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Multiply our big integer by [`UWide`][crate::UWide], wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(multiplication)]
        ///
        /// Many different algorithms were attempted, with a soft [`mulx`] approach
        /// (1), a flat, fixed-width long multiplication (2), and a
        /// short-circuiting long multiplication (3). Algorithm (3) had the best
        /// performance for 128-bit multiplication, however, algorithm (1) was
        /// better for smaller type sizes.
        ///
        /// This also optimized much better when multiplying by a single or a
        /// half-sized item: rather than using 4 limbs, if we're multiplying
        /// `(u128, u128) * u128`, we can use 2 limbs for the right operand, and
        /// for `(u128, u128) * u64`, only 1 limb.
        ///
        /// Using algorithm (3), the addition of `(u128, u128) + (u128, u128)` is in
        /// the worst case 10 `mul` and 13 `add` instructions, while `(u128,
        /// u128) + u64` is always 4 `mul` and 3 `add` instructions without any
        /// branching. This is extremely efficient.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_mul_uwide(self, n: $crate::UWide) -> Self {
            let limbs = $crate::math::mul::wrapping_wide(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`UWide`][crate::UWide], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::wide_doc!(division)]
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!(n)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_rem_uwide(self, n: $crate::UWide) -> (Self, $crate::UWide) {
            let (div, rem) = $crate::math::div::wide(&self.to_le_limbs(), n);
            let div = Self::from_le_limbs(div);
            (div, rem)
        }

        // U32

        /// Add [`u32`] to the big integer, wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_add_u32(self, n: u32) -> Self {
            self.wrapping_add_ulimb(n as $crate::ULimb)
        }

        /// Subtract [`u32`] from the big integer, wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_sub_u32(self, n: u32) -> Self {
            self.wrapping_sub_ulimb(n as $crate::ULimb)
        }

        /// Multiply our big integer by [`u32`], wrapping on
        /// overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(multiplication)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn wrapping_mul_u32(self, n: u32) -> Self {
            self.wrapping_mul_ulimb(n as $crate::ULimb)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by [`u32`], wrapping on overflow.
        ///
        #[doc = $crate::shared::docs::limb_doc!(division)]
        ///
        #[doc = $crate::shared::docs::div_by_zero_doc!(n)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub fn wrapping_div_rem_u32(self, n: u32) -> (Self, u32) {
            let (quo, rem) = self.wrapping_div_rem_ulimb(n as $crate::ULimb);
            (quo, rem as u32)
        }

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
            let (limbs, overflowed) = $crate::math::add::overflowing_limb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Subtract [`ULimb`][crate::ULimb] from the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_sub_ulimb(self, n: $crate::ULimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::sub::overflowing_limb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Multiply our big integer by [`ULimb`][crate::ULimb], returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(multiplication)]
        ///
        /// Many different algorithms were attempted, with a soft [`mulx`] approach
        /// (1), a flat, fixed-width long multiplication (2), and a
        /// short-circuiting long multiplication (3). Algorithm (3) had the best
        /// performance for 128-bit multiplication, however, algorithm (1) was
        /// better for smaller type sizes.
        ///
        /// This also optimized much better when multiplying by a single or a
        /// half-sized item: rather than using 4 limbs, if we're multiplying
        /// `(u128, u128) * u128`, we can use 2 limbs for the right operand, and
        /// for `(u128, u128) * u64`, only 1 limb.
        ///
        /// # Assembly
        ///
        /// The analysis here is practically identical to that of
        /// [`wrapping_mul_ulimb`].
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        /// [`wrapping_mul_ulimb`]: Self::wrapping_mul_ulimb
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_mul_ulimb(self, n: $crate::ULimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::mul::overflowing_limb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        // WIDE

        /// Add [`UWide`][crate::UWide] to the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_add_uwide(self, n: $crate::UWide) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::add::overflowing_wide(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Subtract [`UWide`][crate::UWide] from the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_sub_uwide(self, n: $crate::UWide) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::sub::overflowing_wide(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Multiply our big integer by [`UWide`][crate::UWide], returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::wide_doc!(multiplication)]
        ///
        /// Many different algorithms were attempted, with a soft [`mulx`] approach
        /// (1), a flat, fixed-width long multiplication (2), and a
        /// short-circuiting long multiplication (3). Algorithm (3) had the best
        /// performance for 128-bit multiplication, however, algorithm (1) was
        /// better for smaller type sizes.
        ///
        /// This also optimized much better when multiplying by a single or a
        /// half-sized item: rather than using 4 limbs, if we're multiplying
        /// `(u128, u128) * u128`, we can use 2 limbs for the right operand, and
        /// for `(u128, u128) * u64`, only 1 limb.
        ///
        /// # Assembly
        ///
        /// The analysis here is practically identical to that of
        /// [`wrapping_mul_uwide`].
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        /// [`wrapping_mul_uwide`]: Self::wrapping_mul_uwide
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_mul_uwide(self, n: $crate::UWide) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::mul::overflowing_wide(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        // U32

        /// Add [`u32`] to the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(addition)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_add_u32(self, n: u32) -> (Self, bool) {
            self.overflowing_add_ulimb(n as $crate::ULimb)
        }

        /// Subtract [`u32`] from the big integer, returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(subtraction)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_sub_u32(self, n: u32) -> (Self, bool) {
            self.overflowing_sub_ulimb(n as $crate::ULimb)
        }

        /// Multiply our big integer by [`u32`], returning the value
        /// and if overflow occurred.
        ///
        #[doc = $crate::shared::docs::limb_doc!(multiplication)]
        #[inline(always)]
        #[must_use = $crate::shared::docs::must_use_copy_doc!()]
        pub const fn overflowing_mul_u32(self, n: u32) -> (Self, bool) {
            self.overflowing_mul_ulimb(n as $crate::ULimb)
        }

        // U64

        // TODO: Add

        // U128

        // TODO: Add
    };

    (@checked) => {
        $crate::shared::limb::define!(@checked);
    };

    (@all) => {
        $crate::uint::limb::define!();
        $crate::uint::limb::define!(@wrapping);
        $crate::uint::limb::define!(@overflowing);
        $crate::uint::limb::define!(@checked);
    };
}

pub(crate) use define;
