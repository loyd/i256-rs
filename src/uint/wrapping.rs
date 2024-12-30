//! Overflowing mathmetical operations, which wrap on overflow.

#[rustfmt::skip]
macro_rules! define {
    (signed_type => $s_t:ty, wide_type => $wide_t:ty) => {
        $crate::shared::wrapping::define!(type => $s_t, wide_type => $wide_t);

        /// Wrapping (modular) addition. Computes `self + rhs`,
        /// wrapping around at the boundary of the type.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_add`].")]
        #[inline(always)]
        pub const fn wrapping_add(self, rhs: Self) -> Self {
            let result = $crate::math::add::wrapping_unsigned(&self.to_ne_limbs(), &rhs.to_ne_limbs());
            Self::from_ne_limbs(result)
        }

        /// Wrapping (modular) addition with a signed integer. Computes
        /// `self + rhs`, wrapping around at the boundary of the type.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_add_signed`].")]
        #[inline(always)]
        pub const fn wrapping_add_signed(self, rhs: $s_t) -> Self {
            self.wrapping_add(rhs.as_unsigned())
        }

        /// Wrapping (modular) subtraction. Computes `self - rhs`,
        /// wrapping around at the boundary of the type.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_sub`].")]
        #[inline(always)]
        pub const fn wrapping_sub(self, rhs: Self) -> Self {
            let result = $crate::math::sub::wrapping_unsigned(&self.to_ne_limbs(), &rhs.to_ne_limbs());
            Self::from_ne_limbs(result)
        }

        /// Wrapping (modular) multiplication. Computes `self *
        /// rhs`, wrapping around at the boundary of the type.
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
        /// for `(u128, u128) * u64`, only
        ///
        /// # Assembly
        ///
        /// For a 128-bit multiplication (2x `u64` + 2x `u64`), algorithm (1) had
        /// 6 `mul`, 6 `add`, and 6 bitshift instructions. Algorithm (3) had 10
        /// `mul`, 12 `add`, and 12 bitshift instructions in the worst case, with
        /// a minimum of 4 `mul` and 2 `add` instructions, along with a lot of
        /// branching. That is, it was almost never worth it.
        ///
        /// However, for 256-bit multiplication, the switch flips, with algorithm
        /// (1) having 10 `mul` and 14 `add` instructions. However, algorithm (3)
        /// has in the worst case 10 `mul` and 13 `add` instructions, however,
        /// because of branching in nearly every case, it has better performance
        /// and optimizes nicely for small multiplications.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_mul`].")]
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline(always)]
        pub const fn wrapping_mul(self, rhs: Self) -> Self {
            // 256-Bit
            // -------
            // long_u128:
            //      push    rbp
            //      push    r15
            //      push    r14
            //      push    r13
            //      push    r12
            //      push    rbx
            //      mov     r9, rdx
            //      mov     r15, qword ptr [rdx]
            //      mov     r12, qword ptr [rdx + 8]
            //      mov     rbp, qword ptr [rsi]
            //      mov     r10, qword ptr [rsi + 8]
            //      mov     rax, qword ptr [rsi + 16]
            //      mov     r11, qword ptr [rsi + 24]
            //      mov     r14, rax
            //      mul     r15
            //      mov     qword ptr [rsp - 16], rax
            //      mov     qword ptr [rsp - 8], rdx
            //      imul    r14, r12
            //      mov     rax, r10
            //      mul     r12
            //      mov     r8, rdx
            //      mov     rbx, rax
            //      mov     rax, r10
            //      mul     r15
            //      mov     qword ptr [rsp - 24], rdx
            //      mov     qword ptr [rsp - 32], rax
            //      mov     rax, r12
            //      mul     rbp
            //      mov     r13, rax
            //      mov     rsi, rdx
            //      imul    r11, r15
            //      mov     rax, r15
            //      mul     rbp
            //      mov     r15, rax
            //      mov     r12, rdx
            //      mov     rcx, qword ptr [r9 + 16]
            //      mov     rax, rcx
            //      mul     rbp
            //      imul    r10, rcx
            //      imul    rbp, qword ptr [r9 + 24]
            //      add     rbp, r10
            //      add     r12, r13
            //      adc     rax, rsi
            //      adc     rbp, rdx
            //      add     rax, rbx
            //      adc     r8, 0
            //      add     r14, r11
            //      add     r14, rbp
            //      add     r12, qword ptr [rsp - 32]
            //      adc     rax, qword ptr [rsp - 24]
            //      adc     r14, r8
            //      add     rax, qword ptr [rsp - 16]
            //      adc     r14, qword ptr [rsp - 8]
            //      mov     qword ptr [rdi], r15
            //      mov     qword ptr [rdi + 8], r12
            //      mov     qword ptr [rdi + 16], rax
            //      mov     qword ptr [rdi + 24], r14
            //      mov     rax, rdi
            //      pop     rbx
            //      pop     r12
            //      pop     r13
            //      pop     r14
            //      pop     r15
            //      pop     rbp
            //      ret
            //
            // mulx_u128:
            //     push    rbp
            //     push    r15
            //     push    r14
            //     push    r13
            //     push    r12
            //     push    rbx
            //     mov     r13, rdx
            //     mov     r12, qword ptr [rsp + 56]
            //     mov     r14, qword ptr [rsp + 64]
            //     mov     rax, r12
            //     mul     rsi
            //     mov     qword ptr [rsp - 24], rdx
            //     mov     qword ptr [rsp - 8], rax
            //     mov     rax, r14
            //     mul     rsi
            //     mov     rbx, rax
            //     mov     qword ptr [rsp - 16], rdx
            //     mov     rax, r12
            //     mul     r13
            //     mov     r15, rdx
            //     mov     rbp, rax
            //     mov     rax, r14
            //     mul     r13
            //     mov     r10, rax
            //     mov     r9, rdx
            //     mov     rax, qword ptr [rsp + 72]
            //     imul    r13, rax
            //     mul     rsi
            //     mov     r11, rax
            //     add     rdx, r13
            //     imul    rsi, qword ptr [rsp + 80]
            //     add     rsi, rdx
            //     imul    r8, r12
            //     mov     rax, r12
            //     mul     rcx
            //     add     rdx, r8
            //     imul    r14, rcx
            //     add     r14, rdx
            //     add     rax, r10
            //     adc     r14, r9
            //     add     rax, r11
            //     adc     r14, rsi
            //     add     rbp, qword ptr [rsp - 24]
            //     adc     rax, r15
            //     adc     r14, 0
            //     add     rbp, rbx
            //     adc     rax, qword ptr [rsp - 16]
            //     mov     rcx, qword ptr [rsp - 8]
            //     mov     qword ptr [rdi], rcx
            //     mov     qword ptr [rdi + 8], rbp
            //     mov     qword ptr [rdi + 16], rax
            //     adc     r14, 0
            //     mov     qword ptr [rdi + 24], r14
            //     mov     rax, rdi
            //     pop     rbx
            //     pop     r12
            //     pop     r13
            //     pop     r14
            //     pop     r15
            //     pop     rbp
            //     ret
            let limbs = $crate::math::mul::wrapping_unsigned(&self.to_ne_limbs(), &rhs.to_ne_limbs());
            Self::from_ne_limbs(limbs)
        }

        /// Get the quotient and remainder of our big integer divided
        /// by a signed limb, wrapping on overflow.
        ///
        /// This allows storing of both the quotient and remainder without
        /// making repeated calls.
        ///
        /// # Panics
        ///
        /// This panics if the divisor is 0.
        #[inline]
        pub fn wrapping_div_rem(self, n: Self) -> (Self, Self) {
            // NOTE: Our algorithm assumes little-endian order, which we might not have.
            let x = self.to_le_limbs();
            let y = n.to_le_limbs();

            let (div, rem) = $crate::math::div::full(&x, &y);
            let div = Self::from_le_limbs(div);
            let rem = Self::from_le_limbs(rem);

            (div, rem)
        }

        /// Wrapping (modular) division. Computes `self / rhs`.
        ///
        /// Wrapped division on unsigned types is just normal division. There's
        /// no way wrapping could ever happen. This function exists so that all
        /// operations are accounted for in the wrapping operations.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_div`].")]
        #[inline(always)]
        pub fn wrapping_div(self, rhs: Self) -> Self {
            self.wrapping_div_rem(rhs).0
        }

        /// Wrapping Euclidean division. Computes `self.div_euclid(rhs)`.
        ///
        /// Wrapped division on unsigned types is just normal division. There's
        /// no way wrapping could ever happen. This function exists so that all
        /// operations are accounted for in the wrapping operations. Since, for
        /// the positive integers, all common definitions of division are equal,
        /// this is exactly equal to `self.wrapping_div(rhs)`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_div_euclid`].")]
        #[inline(always)]
        pub fn wrapping_div_euclid(self, rhs: Self) -> Self {
            self.wrapping_div(rhs)
        }

        /// Wrapping (modular) remainder. Computes `self % rhs`.
        ///
        /// Wrapped remainder calculation on unsigned types is just the regular
        /// remainder calculation. There's no way wrapping could ever happen.
        /// This function exists so that all operations are accounted for in the
        /// wrapping operations.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_rem`].")]
        #[inline(always)]
        pub fn wrapping_rem(self, rhs: Self) -> Self {
            self.wrapping_div_rem(rhs).1
        }

        /// Wrapping Euclidean modulo. Computes `self.rem_euclid(rhs)`.
        ///
        /// Wrapped modulo calculation on unsigned types is just the regular
        /// remainder calculation. There's no way wrapping could ever happen.
        /// This function exists so that all operations are accounted for in the
        /// wrapping operations. Since, for the positive integers, all common
        /// definitions of division are equal, this is exactly equal to
        /// `self.wrapping_rem(rhs)`.
        ///
        /// # Panics
        ///
        /// This function will panic if `rhs` is zero.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_rem_euclid`].")]
        #[inline(always)]
        pub fn wrapping_rem_euclid(self, rhs: Self) -> Self {
            self.wrapping_rem(rhs)
        }

        /// Wrapping (modular) negation. Computes `-self`,
        /// wrapping around at the boundary of the type.
        ///
        /// Since unsigned types do not have negative equivalents
        /// all applications of this function will wrap (except for `-0`).
        /// For values smaller than the corresponding signed type's maximum
        /// the result is the same as casting the corresponding signed value.
        /// Any larger values are equivalent to `MAX + 1 - (val - MAX - 1)` where
        /// `MAX` is the corresponding signed type's maximum.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_neg`].")]
        #[inline(always)]
        pub const fn wrapping_neg(self) -> Self {
            Self::MIN.wrapping_sub(self)
        }

        /// Returns the smallest power of two greater than or equal to `n`. If
        /// the next power of two is greater than the type's maximum value,
        /// the return value is wrapped to `0`.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::wrapping_next_power_of_two`].")]
        #[inline]
        pub const fn wrapping_next_power_of_two(self) -> Self {
            self.one_less_than_next_power_of_two().wrapping_add(Self::from_u8(1))
        }
    };
}

pub(crate) use define;
