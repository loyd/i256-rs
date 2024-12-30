//! Operations for our limb operations on big integers.

macro_rules! define {
    () => {
        $crate::shared::limb::define!();
    };

    (@wrapping) => {
        $crate::shared::limb::define!(@wrapping);

        /// Add an unsigned limb to the big integer, wrapping on
        /// overflow.
        ///
        /// This allows optimizations a full addition cannot do.
        #[inline(always)]
        pub const fn wrapping_add_ulimb(self, n: $crate::ULimb) -> Self {
            let limbs = $crate::math::add::wrapping_limb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Subtract an unsigned limb from the big integer, wrapping on
        /// overflow.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn wrapping_sub_ulimb(self, n: $crate::ULimb) -> Self {
            let limbs = $crate::math::sub::wrapping_limb(&self.to_ne_limbs(), n);
            Self::from_ne_limbs(limbs)
        }

        /// Multiply our big integer by an unsigned limb, wrapping on
        /// overflow.
        ///
        /// This allows optimizations a full multiplication cannot do.
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
        /// by an unsigned limb, wrapping on overflow.
        ///
        /// This allows optimizations a full division cannot do.
        ///
        /// # Panics
        ///
        /// This panics if the divisor is 0.
        #[inline(always)]
        pub fn wrapping_div_rem_ulimb(self, n: $crate::ULimb) -> (Self, $crate::ULimb) {
            let x = self.to_le_limbs();
            let (div, rem) = $crate::math::div::limb(&x, n);
            let div = u256::from_le_limbs(div);
            (div, rem)
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
            let (limbs, overflowed) = $crate::math::add::overflowing_limb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Subtract an unsigned limb from the big integer, returning the value
        /// and if overflow occurred.
        ///
        /// This allows optimizations a full subtraction cannot do.
        #[inline(always)]
        pub const fn overflowing_sub_ulimb(self, n: $crate::ULimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::sub::overflowing_limb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }

        /// Multiply our big integer by an unsigned limb, returning the value
        /// and if overflow occurred.
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
        pub const fn overflowing_mul_ulimb(self, n: $crate::ULimb) -> (Self, bool) {
            let (limbs, overflowed) = $crate::math::mul::overflowing_limb(&self.to_ne_limbs(), n);
            (Self::from_ne_limbs(limbs), overflowed)
        }
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
