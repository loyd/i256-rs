//! An unsigned 256-bit integer type.
//!
//! This aims to have feature parity with Rust's unsigned
//! integer types, such as [u32][core::u32]. The documentation
//! is based off of [u32][core::u32] for each method/member.
//!
//! A large portion of the implementation for helper functions
//! are based off of the Rust core implementation, such as for
//! [`checked_pow`][u128::checked_pow], [`isqrt`][u128::isqrt],
//! and more. Any non-performance critical functions, or those
//! crucial to parsing or serialization ([`add`][`u256::add`],
//! [`mul`][`u256::mul`], [`div`][`u256::div`], and
//! [`sub`][`u256::sub`]), as well as their `wrapping_*`,
//! `checked_*`, `overflowing_*` and `*_wide` variants are
//! likely based on the core implementations.

use core::ops::*;

use super::shared_macros::*;
use crate::{i256, math, ULimb, UWide};

int_define!(
    name => u256,
    bits => 256,
    kind => unsigned,
);

impl u256 {
    uint_impl_define!(
        self => u256,
        signed_t => i256,
        signed_wide_t => i128,
        unsigned_wide_t => u128,
        bits => 256,
        max_digits => 78,
        kind => unsigned,
        short_circuit => false,
    );

    /// Shifts the bits to the left by a specified amount, `n`,
    /// wrapping the truncated bits to the end of the resulting integer.
    ///
    /// Please note this isn't the same operation as the `<<` shifting operator!
    ///
    /// See [`u128::rotate_left`].
    #[inline(always)]
    pub const fn rotate_left(self, n: u32) -> Self {
        let (lo, hi) = math::rotate_left_u128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Shifts the bits to the right by a specified amount, `n`,
    /// wrapping the truncated bits to the beginning of the resulting
    /// integer.
    ///
    /// Please note this isn't the same operation as the `>>` shifting operator!
    ///
    /// See [`u128::rotate_right`].
    #[inline(always)]
    pub const fn rotate_right(self, n: u32) -> Self {
        let (lo, hi) = math::rotate_right_u128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Wrapping (modular) addition. Computes `self + rhs`,
    /// wrapping around at the boundary of the type.
    ///
    /// See [`u128::wrapping_add`].
    #[inline(always)]
    pub const fn wrapping_add(self, rhs: Self) -> Self {
        let (lo, hi) = math::wrapping_add_u128(self.low(), self.high(), rhs.low(), rhs.high());
        u256::new(lo, hi)
    }

    /// Wrapping (modular) addition with a signed integer. Computes
    /// `self + rhs`, wrapping around at the boundary of the type.
    ///
    /// See [`u128::wrapping_add_signed`].
    #[inline(always)]
    pub const fn wrapping_add_signed(self, rhs: i256) -> Self {
        self.wrapping_add(Self::from_i256(rhs))
    }

    /// Wrapping (modular) subtraction. Computes `self - rhs`,
    /// wrapping around at the boundary of the type.
    ///
    /// See [`u128::wrapping_sub`].
    #[inline(always)]
    pub const fn wrapping_sub(self, rhs: Self) -> Self {
        let (lo, hi) = math::wrapping_sub_u128(self.low(), self.high(), rhs.low(), rhs.high());
        u256::new(lo, hi)
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
    /// has in the worst case 10 `mul` and 15 `add` instructions, however,
    /// because of branching in nearly every case, it has better performance
    /// and optimizes nicely for small multiplications.
    ///
    /// See [`u128::wrapping_mul`].
    ///
    /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
    #[inline(always)]
    pub const fn wrapping_mul(self, rhs: Self) -> Self {
        // 128-Bit
        // -------
        // long_u64:
        //     push    r15
        //     push    r14
        //     push    rbx
        //     mov     r11, rdi
        //     shr     r11, 32
        //     mov     r8, rdx
        //     shr     r8, 32
        //     test    edi, edi
        //     je      .LBB0_1
        //     mov     ebx, edi
        //     mov     r9, rcx
        //     shr     r9, 32
        //     mov     eax, edx
        //     imul    rax, rbx
        //     mov     r10d, eax
        //     mov     r14, rax
        //     shr     r14, 32
        //     mov     rax, r8
        //     imul    rax, rbx
        //     add     rax, r14
        //     mov     r14, rax
        //     shr     r14, 32
        //     mov     r15d, ecx
        //     imul    r15, rbx
        //     imul    r9d, edi
        //     shl     r9, 32
        //     add     r9, r15
        //     add     r9, r14
        //     movabs  rdi, -4294967296
        //     test    r11, r11
        //     je      .LBB0_5
        // .LBB0_4:
        //     mov     ebx, edx
        //     imul    rbx, r11
        //     mov     eax, eax
        //     add     rax, rbx
        //     mov     rbx, rax
        //     shr     rbx, 32
        //     mov     r14, r8
        //     imul    r14, r11
        //     mov     r15d, r9d
        //     add     r15, r14
        //     add     r15, rbx
        //     mov     ebx, r15d
        //     imul    r11d, ecx
        //     shl     r11, 32
        //     add     r11, r15
        //     and     r11, rdi
        //     add     r11, r9
        //     and     r11, rdi
        //     or      r11, rbx
        //     mov     r9, r11
        // .LBB0_5:
        //     test    esi, esi
        //     je      .LBB0_7
        //     mov     ecx, esi
        //     mov     r11d, edx
        //     imul    r11, rcx
        //     mov     ecx, r9d
        //     add     rcx, r11
        //     mov     r11d, ecx
        //     imul    r8d, esi
        //     shl     r8, 32
        //     add     r8, rcx
        //     and     r8, rdi
        //     add     r8, r9
        //     and     r8, rdi
        //     or      r8, r11
        //     mov     r9, r8
        // .LBB0_7:
        //     shr     rsi, 32
        //     imul    edx, esi
        //     shl     rdx, 32
        //     test    rsi, rsi
        //     cmove   rdx, rsi
        //     add     rdx, r9
        //     shl     rax, 32
        //     or      rax, r10
        //     pop     rbx
        //     pop     r14
        //     pop     r15
        //     ret
        // .LBB0_1:
        //     xor     r9d, r9d
        //     xor     eax, eax
        //     xor     r10d, r10d
        //     movabs  rdi, -4294967296
        //     test    r11, r11
        //     jne     .LBB0_4
        //     jmp     .LBB0_5
        //
        // mulx_u64:
        //     mov     eax, edi
        //     imul    rcx, rdi
        //     shr     rdi, 32
        //     mov     r8d, edx
        //     mov     r9, rdx
        //     shr     r9, 32
        //     mov     r10, r8
        //     imul    r10, rax
        //     imul    rax, r9
        //     imul    r8, rdi
        //     imul    r9, rdi
        //     mov     edi, r10d
        //     shr     r10, 32
        //     add     r10, r8
        //     mov     r8d, r10d
        //     shr     r10, 32
        //     add     r8, rax
        //     mov     rax, r8
        //     shl     rax, 32
        //     or      rax, rdi
        //     shr     r8, 32
        //     imul    rdx, rsi
        //     add     rdx, rcx
        //     add     rdx, r9
        //     add     rdx, r10
        //     add     rdx, r8
        //     ret
        //
        // 256-Bit
        // -------
        // long_u128:
        //     push    r15
        //     push    r14
        //     push    r13
        //     push    r12
        //     push    rbx
        //     mov     r12, rdx
        //     mov     r15, qword ptr [rsp + 64]
        //     mov     r11, qword ptr [rsp + 56]
        //     mov     rbx, qword ptr [rsp + 48]
        //     test    rsi, rsi
        //     je      .LBB1_1
        //     mov     rax, rbx
        //     mul     rsi
        //     mov     r14, rdx
        //     mov     r9, rax
        //     mov     rax, r11
        //     mul     rsi
        //     mov     r13, rdx
        //     mov     r10, rax
        //     add     r10, r14
        //     adc     r13, 0
        //     mov     rax, r15
        //     mul     rsi
        //     mov     r14, rax
        //     imul    rsi, qword ptr [rsp + 72]
        //     add     r14, r13
        //     adc     rsi, rdx
        //     test    r12, r12
        //     je      .LBB1_5
        // .LBB1_4:
        //     mov     rax, rbx
        //     mul     r12
        //     mov     r13, rdx
        //     add     r10, rax
        //     adc     r13, 0
        //     mov     rax, r11
        //     mul     r12
        //     add     rax, r13
        //     adc     rdx, 0
        //     imul    r15, r12
        //     add     r14, rax
        //     adc     r15, rdx
        //     add     rsi, r15
        // .LBB1_5:
        //     test    rcx, rcx
        //     je      .LBB1_7
        //     mov     rax, rbx
        //     mul     rcx
        //     imul    r11, rcx
        //     add     r14, rax
        //     adc     r11, rdx
        //     add     rsi, r11
        // .LBB1_7:
        //     test    r8, r8
        //     je      .LBB1_9
        //     imul    r8, rbx
        //     add     rsi, r8
        // .LBB1_9:
        //     mov     qword ptr [rdi + 8], r10
        //     mov     qword ptr [rdi], r9
        //     mov     qword ptr [rdi + 24], rsi
        //     mov     qword ptr [rdi + 16], r14
        //     mov     rax, rdi
        //     pop     rbx
        //     pop     r12
        //     pop     r13
        //     pop     r14
        //     pop     r15
        //     ret
        // .LBB1_1:
        //     xor     esi, esi
        //     xor     r14d, r14d
        //     xor     r10d, r10d
        //     xor     r9d, r9d
        //     test    r12, r12
        //     jne     .LBB1_4
        //     jmp     .LBB1_5
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
        let r = math::wrapping_mul_arr_u128(&self.to_le_limbs(), &rhs.to_le_limbs());
        Self::from_le_limbs(r)
    }

    /// Panic-free bitwise shift-left; yields `self << mask(rhs)`,
    /// where `mask` removes any high-order bits of `rhs` that
    /// would cause the shift to exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-left; the
    /// RHS of a wrapping shift-left is restricted to the range
    /// of the type, rather than the bits shifted out of the LHS
    /// being returned to the other end. The primitive integer
    /// types all implement a [`rotate_left`](Self::rotate_left) function,
    /// which may be what you want instead.
    ///
    /// See [`u128::wrapping_shl`].
    #[inline(always)]
    pub const fn wrapping_shl(self, rhs: u32) -> Self {
        let (lo, hi) = math::shl_u128(self.low(), self.high(), rhs % 256);
        Self::new(lo, hi)
    }

    /// Panic-free bitwise shift-right; yields `self >> mask(rhs)`,
    /// where `mask` removes any high-order bits of `rhs` that
    /// would cause the shift to exceed the bitwidth of the type.
    ///
    /// Note that this is *not* the same as a rotate-right; the
    /// RHS of a wrapping shift-right is restricted to the range
    /// of the type, rather than the bits shifted out of the LHS
    /// being returned to the other end. The primitive integer
    /// types all implement a [`rotate_right`](Self::rotate_right) function,
    /// which may be what you want instead.
    ///
    /// See [`u128::wrapping_shr`].
    #[inline(always)]
    pub const fn wrapping_shr(self, rhs: u32) -> Self {
        let (lo, hi) = math::shr_u128(self.low(), self.high(), rhs % 256);
        Self::new(lo, hi)
    }

    /// Calculates `self` + `rhs`.
    ///
    /// Returns a tuple of the addition along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    ///
    /// See [`u128::overflowing_add`].
    #[inline(always)]
    pub const fn overflowing_add(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) =
            math::overflowing_add_u128(self.low(), self.high(), rhs.low(), rhs.high());
        (Self::new(lo, hi), overflowed)
    }

    /// Calculates `self` - `rhs`.
    ///
    /// Returns a tuple of the subtraction along with a boolean indicating
    /// whether an arithmetic overflow would occur. If an overflow would
    /// have occurred then the wrapped value is returned.
    ///
    /// See [`u128::overflowing_sub`].
    #[inline(always)]
    pub const fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
        let (lo, hi, overflowed) =
            math::overflowing_sub_u128(self.low(), self.high(), rhs.low(), rhs.high());
        (Self::new(lo, hi), overflowed)
    }

    /// Calculates the multiplication of `self` and `rhs`.
    ///
    /// Returns a tuple of the multiplication along with a boolean
    /// indicating whether an arithmetic overflow would occur. If an
    /// overflow would have occurred then the wrapped value is returned.
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
    /// * `x0` - The lower half of x.
    /// * `x1` - The upper half of x.
    /// * `y0` - The lower half of y.
    /// * `y1` - The upper half of y.
    ///
    /// # Assembly
    ///
    /// The analysis here is practically identical to that of [`wrapping_mul`].
    ///
    /// See [`u128::overflowing_mul`].
    ///
    /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
    /// [`wrapping_mul`]: Self::wrapping_mul
    #[inline(always)]
    pub const fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
        let (r, overflow) = math::overflowing_mul_arr_u128(&self.to_le_limbs(), &rhs.to_le_limbs());
        (Self::from_le_limbs(r), overflow)
    }

    from_str_radix_define!(false);
    to_str_radix_define!(false);
}

impl u256 {
    /// Create the 256-bit unsigned integer from a `u128`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_u128(value: u128) -> Self {
        let (lo, hi) = math::as_uwide_u128(value);
        Self::new(lo, hi)
    }

    /// Create the 256-bit unsigned integer from a `u256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_u256(value: u256) -> Self {
        value
    }

    /// Create the 256-bit unsigned integer from a `u256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_unsigned(value: u256) -> Self {
        Self::from_u256(value)
    }

    /// Create the 256-bit unsigned integer from an `i128`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_i128(value: i128) -> Self {
        let (lo, hi) = math::as_iwide_u128(value);
        Self::new(lo, hi)
    }

    /// Create the 256-bit unsigned integer from an `i256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_i256(value: i256) -> Self {
        value.as_u256()
    }

    /// Create the 256-bit unsigned integer from an `i256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn from_signed(value: i256) -> Self {
        Self::from_i256(value)
    }

    /// Convert the 256-bit unsigned integer to an `u128`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_u128(&self) -> u128 {
        math::as_unarrow_u128(self.low(), self.high())
    }

    /// Convert the 256-bit unsigned integer to an `u256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_u256(&self) -> Self {
        *self
    }

    /// Convert the 256-bit unsigned integer to an `u256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_unsigned(&self) -> Self {
        self.as_u256()
    }

    /// Convert the 256-bit unsigned integer to an `i128`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_i128(&self) -> i128 {
        math::as_inarrow_u128(self.low(), self.high())
    }

    /// Convert the 256-bit unsigned integer to an `i256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_i256(&self) -> i256 {
        let (lo, hi) = math::wide_cast_u128(self.low(), self.high());
        i256::new(lo, hi)
    }

    /// Convert the 256-bit unsigned integer to an `i256`, as if by an `as`
    /// cast.
    #[inline(always)]
    pub const fn as_signed(&self) -> i256 {
        self.as_i256()
    }

    /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn wrapping_add_uwide(self, n: UWide) -> Self {
        let (lo, hi) = math::wrapping_add_wide_u128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Add the 256-bit integer by a wide, 128-bit unsigned factor.
    /// This allows optimizations a full addition cannot do.
    #[inline(always)]
    pub const fn overflowing_add_uwide(self, n: UWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_add_wide_u128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn wrapping_sub_uwide(self, n: UWide) -> Self {
        let (lo, hi) = math::wrapping_sub_wide_u128(self.low(), self.high(), n);
        Self::new(lo, hi)
    }

    /// Subtract the 256-bit integer by a wide, 128-bit unsigned factor.
    /// This allows optimizations a full subtraction cannot do.
    #[inline(always)]
    pub const fn overflowing_sub_uwide(self, n: UWide) -> (Self, bool) {
        let (lo, hi, overflowed) = math::overflowing_sub_wide_u128(self.low(), self.high(), n);
        (Self::new(lo, hi), overflowed)
    }

    /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
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
    /// # Assembly
    ///
    /// Using algorithm (3), the addition of `(u128, u128) + (u128, u128)` is in
    /// the worst case 10 `mul` and 15 `add` instructions, while `(u128,
    /// u128) + u128` is at worst 8 `mul` and 12 `add` instructions, which
    /// optimizes quite nicely.
    ///
    /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
    #[inline(always)]
    pub const fn wrapping_mul_uwide(self, n: UWide) -> Self {
        // 256-Bit
        // -------
        // wrapping_mul:
        //     push    r15
        //     push    r14
        //     push    r12
        //     push    rbx
        //     mov     r14, rdx
        //     mov     r11, qword ptr [rsp + 48]
        //     mov     rbx, qword ptr [rsp + 40]
        //     test    rsi, rsi
        //     je      .LBB1_1
        //     mov     rax, rbx
        //     mul     rsi
        //     mov     r12, rdx
        //     mov     r15, rax
        //     mov     rax, r11
        //     mul     rsi
        //     mov     r10, rdx
        //     mov     r9, rax
        //     add     r9, r12
        //     adc     r10, 0
        //     test    r14, r14
        //     jne     .LBB1_5
        // .LBB1_4:
        //     xor     r14d, r14d
        //     test    rcx, rcx
        //     jne     .LBB1_7
        //     jmp     .LBB1_8
        // .LBB1_1:
        //     xor     r9d, r9d
        //     xor     r15d, r15d
        //     xor     r10d, r10d
        //     test    r14, r14
        //     je      .LBB1_4
        // .LBB1_5:
        //     mov     rax, rbx
        //     mul     r14
        //     mov     rsi, rdx
        //     add     r9, rax
        //     adc     rsi, 0
        //     mov     rax, r11
        //     mul     r14
        //     mov     r14, rdx
        //     add     rax, rsi
        //     adc     r14, 0
        //     add     r10, rax
        //     adc     r14, 0
        //     test    rcx, rcx
        //     je      .LBB1_8
        // .LBB1_7:
        //     mov     rax, rbx
        //     mul     rcx
        //     imul    r11, rcx
        //     add     r10, rax
        //     adc     r11, rdx
        //     add     r14, r11
        // .LBB1_8:
        //     test    r8, r8
        //     je      .LBB1_10
        //     imul    r8, rbx
        //     add     r14, r8
        // .LBB1_10:
        //     mov     qword ptr [rdi + 8], r9
        //     mov     qword ptr [rdi], r15
        //     mov     qword ptr [rdi + 24], r14
        //     mov     qword ptr [rdi + 16], r10
        //     mov     rax, rdi
        //     pop     rbx
        //     pop     r12
        //     pop     r14
        //     pop     r15
        //     ret
        let n = math::split!(UWide, ULimb, n);
        let r = math::wrapping_mul_arr_u128(&self.to_le_limbs(), &n);
        Self::from_le_limbs(r)
    }

    /// Multiply the 256-bit integer by a wide, 128-bit unsigned factor.
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
    /// # Assembly
    ///
    /// The analysis here is practically identical to that of
    /// [`wrapping_mul_uwide`].
    ///
    /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
    /// [`wrapping_mul_uwide`]: Self::wrapping_mul_uwide
    #[inline(always)]
    pub const fn overflowing_mul_uwide(self, n: UWide) -> (Self, bool) {
        let n = math::split!(UWide, ULimb, n);
        let (r, overflow) = math::overflowing_mul_arr_u128(&self.to_le_limbs(), &n);
        (Self::from_le_limbs(r), overflow)
    }

    /// Multiply the 256-bit integer by a 64-bit unsigned factor.
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
    /// the worst case 10 `mul` and 15 `add` instructions, while `(u128,
    /// u128) + u64` is always 4 `mul` and 3 `add` instructions without any
    /// branching. This is extremely efficient.
    ///
    /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
    #[inline(always)]
    pub const fn wrapping_mul_ulimb(self, n: ULimb) -> Self {
        // 256-Bit
        // -------
        // wrapping_mul:
        //     push    rbx
        //     mov     rax, rcx
        //     mov     rcx, rdx
        //     imul    r8, r9
        //     mul     r9
        //     mov     r10, rdx
        //     mov     r11, rax
        //     mov     rax, rcx
        //     mul     r9
        //     mov     rcx, rdx
        //     mov     rbx, rax
        //     mov     rax, rsi
        //     mul     r9
        //     add     rdx, rbx
        //     adc     rcx, r11
        //     adc     r10, r8
        //     mov     qword ptr [rdi], rax
        //     mov     qword ptr [rdi + 8], rdx
        //     mov     qword ptr [rdi + 16], rcx
        //     mov     qword ptr [rdi + 24], r10
        //     mov     rax, rdi
        //     pop     rbx
        //     ret
        let r = math::wrapping_mul_arr_u128(&self.to_le_limbs(), &[n]);
        Self::from_le_limbs(r)
    }

    /// Multiply the 256-bit integer by a 64-bit unsigned factor.
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
    pub const fn overflowing_mul_ulimb(self, n: ULimb) -> (Self, bool) {
        let (r, overflow) = math::overflowing_mul_arr_u128(&self.to_le_limbs(), &[n]);
        (Self::from_le_limbs(r), overflow)
    }

    /// Div/Rem the 256-bit integer by a wide, 128-bit unsigned factor.
    ///
    /// This is a convenience function: always prefer [`wrapping_div_rem`]
    /// or [`wrapping_div_rem_ulimb`] if possible.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    ///
    /// [`wrapping_div_rem`]: Self::wrapping_div_rem
    /// [`wrapping_div_rem_ulimb`]: Self::wrapping_div_rem_ulimb
    #[inline(always)]
    pub fn wrapping_div_rem_uwide(self, n: UWide) -> (Self, UWide) {
        let x = self.to_le_limbs();
        let (div, rem) = math::div_rem_wide(&x, n);
        let div = u256::from_le_limbs(div);
        (div, rem)
    }

    /// Div/Rem the 256-bit integer by a 64-bit unsigned factor.
    ///
    /// This allows optimizations a full division cannot do.
    ///
    /// # Panics
    ///
    /// This panics if the divisor is 0.
    #[inline(always)]
    pub fn wrapping_div_rem_ulimb(self, n: ULimb) -> (Self, ULimb) {
        let x = self.to_le_limbs();
        let (div, rem) = math::div_rem_limb(&x, n);
        let div = u256::from_le_limbs(div);
        (div, rem)
    }
}

uint_traits_define!(type => u256, signed_type => i256);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ParseIntError;

    #[test]
    fn add_test() {
        // NOTE: This is mostly covered elsewhere
        assert_eq!(u256::from_u8(1).wrapping_add(u256::from_u8(1)), u256::from_u8(2));
        assert_eq!(u256::MAX.wrapping_add(u256::MAX), u256::new(u128::MAX - 1, u128::MAX));

        assert_eq!(
            u256::from_u8(1).overflowing_add(u256::from_u8(1)).0,
            u256::from_u8(1).wrapping_add(u256::from_u8(1))
        );
        assert_eq!(u256::MAX.overflowing_add(u256::MAX).0, u256::MAX.wrapping_add(u256::MAX));
    }

    #[test]
    fn display_test() {
        let max = u256::MAX;
        let result = max.to_string();
        assert_eq!(
            "115792089237316195423570985008687907853269984665640564039457584007913129639935",
            result
        );

        let value = u256::new(0, 1);
        let result = value.to_string();
        assert_eq!("340282366920938463463374607431768211456", result);
    }

    #[test]
    fn lower_exp_test() {
        let max = u256::MAX;
        let result = format!("{:e}", max);
        assert_eq!(
            "1.15792089237316195423570985008687907853269984665640564039457584007913129639935e77",
            result
        );

        let value = u256::new(0, 1);
        let result = format!("{:e}", value);
        assert_eq!("3.40282366920938463463374607431768211456e38", result);
    }

    #[test]
    fn upper_exp_test() {
        let max = u256::MAX;
        let result = format!("{:E}", max);
        assert_eq!(
            "1.15792089237316195423570985008687907853269984665640564039457584007913129639935E77",
            result
        );

        let value = u256::new(0, 1);
        let result = format!("{:E}", value);
        assert_eq!("3.40282366920938463463374607431768211456E38", result);
    }

    #[test]
    fn octal_test() {
        let max = u256::MAX;
        let result = format!("{:o}", max);
        assert_eq!(
            "17777777777777777777777777777777777777777777777777777777777777777777777777777777777777",
            result
        );

        let result = format!("{:#o}", max);
        assert_eq!(
            "0o17777777777777777777777777777777777777777777777777777777777777777777777777777777777777",
            result
        );

        let value = u256::new(0, 1);
        let result = format!("{:o}", value);
        assert_eq!("4000000000000000000000000000000000000000000", result);
    }

    #[test]
    fn binary_test() {
        let max = u256::MAX;
        let result = format!("{:b}", max);
        assert_eq!(
            "1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111",
            result
        );

        let result = format!("{:#b}", max);
        assert_eq!(
            "0b1111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111111",
            result
        );

        let value = u256::new(0, 1);
        let result = format!("{:b}", value);
        assert_eq!(
            "100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000",
            result
        );
    }

    #[test]
    fn lower_hex_test() {
        let max = u256::MAX;
        let result = format!("{:x}", max);
        assert_eq!("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", result);

        let result = format!("{:#x}", max);
        assert_eq!("0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", result);

        let value = u256::new(0, 1);
        let result = format!("{:x}", value);
        assert_eq!("100000000000000000000000000000000", result);
    }

    #[test]
    fn upper_hex_test() {
        let max = u256::MAX;
        let result = format!("{:X}", max);
        assert_eq!("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", result);

        let result = format!("{:#X}", max);
        assert_eq!("0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", result);

        let value = u256::new(0, 1);
        let result = format!("{:X}", value);
        assert_eq!("100000000000000000000000000000000", result);
    }

    #[inline(always)]
    fn parse(expected: u256, radix: u32, s: &str) {
        // check a full roundtrip
        let res: Result<u256, ParseIntError> = u256::from_str_radix(s, radix);
        assert!(res.is_ok());
        let actual = res.unwrap();
        assert_eq!(expected, actual);

        let as_str = actual.to_string();
        let res: Result<u256, ParseIntError> = u256::from_str_radix(&as_str, 10);
        assert!(res.is_ok());
        let actual = res.unwrap();
        assert_eq!(expected, actual);
    }

    #[test]
    fn from_str_radix_test() {
        let cases = [
            (
                u256::MAX,
                10,
                "115792089237316195423570985008687907853269984665640564039457584007913129639935",
            ),
            (
                u256::MAX,
                10,
                "+115792089237316195423570985008687907853269984665640564039457584007913129639935",
            ),
            (u256::MAX, 16, "+ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff"),
            (0xffffffffffffffffu128.into(), 16, "+ffffffffffffffff"),
            (0x123456789ab123u128.into(), 10, "5124095576027427"),
            (0x123456789ab123u128.into(), 16, "+123456789ab123"),
        ];
        for case in cases {
            parse(case.0, case.1, case.2);
        }

        let failing = [
            (10, "-15"),
            (16, "-0xFF"),
            (16, "+0xFF"),
            (16, "0xFF"),
            (10, "FF"),
            (10, "a9"),
            (10, "12.34"),
            (10, "1234_67"),
            (10, "115792089237316195423570985008687907853269984665640564039457584007913129639936"),
        ];
        for case in failing {
            let res: Result<u256, ParseIntError> = u256::from_str_radix(case.1, case.0);
            assert!(res.is_err());
        }
    }

    #[test]
    #[should_panic]
    fn from_str_radix_neg_test() {
        _ = u256::from_str_radix("-123", 10).unwrap();
    }
}
