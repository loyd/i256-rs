//! Arithmetic utilities from small, native integer components.
//!
//! This allows the construction of larger type sizes from native,
//! fast integers.

#![doc(hidden)]

// NOTE: Division and remainders aren't supported due to the difficulty in
// implementation. See `div.rs` for the implementation.

/// Check if an array stored unsigned values is negative.
#[doc(hidden)]
#[macro_export]
macro_rules! is_negative {
    ($x:ident, $s:ty) => {{
        let msl = ne_index!($x[$x.len() - 1]) as $s;
        msl < 0
    }};
}

/// Negate a given value, via a carrying add.
#[doc(hidden)]
#[macro_export]
macro_rules! negate {
    ($x:ident, $n:expr, $t:ty) => {{
        let mut result = [0; $n];
        let x0 = !ne_index!($x[0]);
        let (mut v, mut c) = x0.overflowing_add(1);
        ne_index!(result[0] = v);

        let mut index = 1;
        while index < $n - 1 {
            let xi = !ne_index!($x[index]);
            (v, c) = xi.overflowing_add(c as $t);
            ne_index!(result[index] = v);
            index += 1;
        }

        if $n > 1 {
            let xn = !ne_index!($x[index]);
            v = xn.wrapping_add(c as $t);
            ne_index!(result[index] = v);
        }

        result
    }};
}

// BINARY OPS - UNSIGNED
// ---------------------

macro_rules! add_unsigned_impl {
    (
        $u:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_limb =>
        $wrapping_limb:ident,overflowing_limb =>
        $overflowing_limb:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_add` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 256-bit addition (4x u64 + 4x u64), it optimizes to 1
        /// `add` and 3 `adc` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     mov     rcx, qword ptr [rsi]
        ///     mov     rdi, qword ptr [rsi + 8]
        ///     add     rcx, qword ptr [rdx]
        ///     mov     r8, qword ptr [rsi + 16]
        ///     adc     rdi, qword ptr [rdx + 8]
        ///     mov     r9, qword ptr [rdx + 24]
        ///     adc     r8, qword ptr [rdx + 16]
        ///     adc     r9, qword ptr [rsi + 24]
        ///     mov     qword ptr [rax], rcx
        ///     mov     qword ptr [rax + 8], rdi
        ///     mov     qword ptr [rax + 16], r8
        ///     mov     qword ptr [rax + 24], r9
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_full<const N: usize>(x: &[$u; N], y: &[$u; N]) -> [$u; N] {
            // FIXME: Move to `carrying_add` once stable.
            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            while index < N - 1 {
                let (vi, c0) = ne_index!(x[index]).overflowing_add(ne_index!(y[index]));
                let (vi, c1) = vi.overflowing_add(c as $u);
                ne_index!(result[index] = vi);
                c = c0 | c1;
                index += 1;
            }

            let vn = ne_index!(x[index]).wrapping_add(ne_index!(y[index]));
            ne_index!(result[index] = vn.wrapping_add(c as $u));

            result
        }

        /// Const implementation of `overflowing_add` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 256-bit addition (4x u64 + 4x u64), it optimizes to 1
        /// `add`, 3 `adc`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     mov     rcx, qword ptr [rsi]
        ///     add     rcx, qword ptr [rdx]
        ///     mov     rdi, qword ptr [rsi + 8]
        ///     adc     rdi, qword ptr [rdx + 8]
        ///     mov     r8, qword ptr [rsi + 16]
        ///     adc     r8, qword ptr [rdx + 16]
        ///     mov     rsi, qword ptr [rsi + 24]
        ///     adc     rsi, qword ptr [rdx + 24]
        ///     mov     qword ptr [rax], rcx
        ///     mov     qword ptr [rax + 8], rdi
        ///     mov     qword ptr [rax + 16], r8
        ///     mov     qword ptr [rax + 24], rsi
        ///     setb    byte ptr [rax + 32]
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_full<const N: usize>(
            x: &[$u; N],
            y: &[$u; N],
        ) -> ([$u; N], bool) {
            // FIXME: Move to `carrying_add` once stable.
            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            while index < N - 1 {
                let (vi, c0) = ne_index!(x[index]).overflowing_add(ne_index!(y[index]));
                let (vi, c1) = vi.overflowing_add(c as $u);
                ne_index!(result[index] = vi);
                c = c0 | c1;
                index += 1;
            }

            let (vn, c0) = ne_index!(x[index]).overflowing_add(ne_index!(y[index]));
            let (vn, c1) = vn.overflowing_add(c as $u);
            ne_index!(result[index] = vn);

            (result, c0 | c1)
        }

        /// Const implementation of `wrapping_add` a small number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 1
        /// `add` and 3 `adc` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     mov     rcx, qword ptr [rsi + 8]
        ///     mov     rdi, qword ptr [rsi + 16]
        ///     add     rdx, qword ptr [rsi]
        ///     adc     rcx, 0
        ///     adc     rdi, 0
        ///     mov     rsi, qword ptr [rsi + 24]
        ///     adc     rsi, 0
        ///     mov     qword ptr [rax], rdx
        ///     mov     qword ptr [rax + 8], rcx
        ///     mov     qword ptr [rax + 16], rdi
        ///     mov     qword ptr [rax + 24], rsi
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_limb<const N: usize>(x: &[$u; N], y: $u) -> [$u; N] {
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let (mut v, mut c) = ne_index!(x[index]).overflowing_add(y);
            ne_index!(result[index] = v);
            index += 1;
            // NOTE: Do not branch anywhere in here, it decimates performance.
            while index < N - 1 {
                (v, c) = ne_index!(x[index]).overflowing_add(c as $u);
                ne_index!(result[index] = v);
                index += 1;
            }

            v = ne_index!(x[index]).wrapping_add(c as $u);
            ne_index!(result[index] = v);

            result
        }

        /// Const implementation of `overflowing_add` a small number to the wider type.
        ///
        /// Returns the value, wrapping on overflow, and if the add overflowed.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 1
        /// `add`, 3 `adc`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     mov     rcx, qword ptr [rsi + 8]
        ///     mov     rdi, qword ptr [rsi + 16]
        ///     mov     r8, qword ptr [rsi + 24]
        ///     add     rdx, qword ptr [rsi]
        ///     adc     rcx, 0
        ///     adc     rdi, 0
        ///     adc     r8, 0
        ///     mov     qword ptr [rax], rdx
        ///     mov     qword ptr [rax + 8], rcx
        ///     mov     qword ptr [rax + 16], rdi
        ///     mov     qword ptr [rax + 24], r8
        ///     setb    byte ptr [rax + 32]
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_limb<const N: usize>(x: &[$u; N], y: $u) -> ([$u; N], bool) {
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let (mut v, mut c) = ne_index!(x[index]).overflowing_add(y);
            ne_index!(result[index] = v);
            index += 1;
            while index < N - 1 {
                (v, c) = ne_index!(x[index]).overflowing_add(c as $u);
                ne_index!(result[index] = v);
                index += 1;
            }

            (v, c) = ne_index!(x[index]).overflowing_add(c as $u);
            ne_index!(result[index] = v);

            (result, c)
        }
    };
}

add_unsigned_impl!(
    u32,
    wrapping_full => wrapping_add_u32,
    overflowing_full => overflowing_add_u32,
    wrapping_limb => wrapping_add_limb_u32,
    overflowing_limb => overflowing_add_limb_u32
);
add_unsigned_impl!(
    u64,
    wrapping_full => wrapping_add_u64,
    overflowing_full => overflowing_add_u64,
    wrapping_limb => wrapping_add_limb_u64,
    overflowing_limb => overflowing_add_limb_u64
);

macro_rules! sub_unsigned_impl {
    (
        $u:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_limb =>
        $wrapping_limb:ident,overflowing_limb =>
        $overflowing_limb:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_sub` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on `x86_64`,
        /// for a 256-bit subtraction (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `sub` and 3 `sbb` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, rdi
        ///     mov     rcx, qword ptr [rsi + 16]
        ///     mov     rdi, qword ptr [rsi]
        ///     sub     rdi, qword ptr [rdx]
        ///     mov     r8, qword ptr [rsi + 8]
        ///     sbb     r8, qword ptr [rdx + 8]
        ///     sbb     rcx, qword ptr [rdx + 16]
        ///     mov     rsi, qword ptr [rsi + 24]
        ///     sbb     rsi, qword ptr [rdx + 24]
        ///     mov     qword ptr [rax], rdi
        ///     mov     qword ptr [rax + 8], r8
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], rsi
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_full<const N: usize>(x: &[$u; N], y: &[$u; N]) -> [$u; N] {
            // FIXME: Move to `borrowing_sub` once stable.
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            while index < N - 1 {
                let (vi, c0) = ne_index!(x[index]).overflowing_sub(ne_index!(y[index]));
                let (vi, c1) = vi.overflowing_sub(c as $u);
                ne_index!(result[index] = vi);
                c = c0 | c1;
                index += 1;
            }

            let vn = ne_index!(x[index]).wrapping_sub(ne_index!(y[index]));
            ne_index!(result[index] = vn.wrapping_sub(c as $u));

            result
        }

        /// Const implementation of `overflowing_sub` for internal algorithm use.
        ///
        /// Returns the value and if the sub underflowed.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit subtraction (2x u128 + 2x u128), it optimizes to 1
        /// `sub`, 3 `sbb`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     mov     rcx, qword ptr [rsi]
        ///     sub     rcx, qword ptr [rdx]
        ///     mov     rdi, qword ptr [rsi + 8]
        ///     sbb     rdi, qword ptr [rdx + 8]
        ///     mov     r8, qword ptr [rsi + 16]
        ///     sbb     r8, qword ptr [rdx + 16]
        ///     mov     rsi, qword ptr [rsi + 24]
        ///     sbb     rsi, qword ptr [rdx + 24]
        ///     mov     qword ptr [rax], rcx
        ///     mov     qword ptr [rax + 8], rdi
        ///     mov     qword ptr [rax + 16], r8
        ///     mov     qword ptr [rax + 24], rsi
        ///     setb    byte ptr [rax + 32]
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_full<const N: usize>(
            x: &[$u; N],
            y: &[$u; N],
        ) -> ([$u; N], bool) {
            // FIXME: Move to `borrowing_sub` once stable.
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            while index < N - 1 {
                let (vi, c0) = ne_index!(x[index]).overflowing_sub(ne_index!(y[index]));
                let (vi, c1) = vi.overflowing_sub(c as $u);
                ne_index!(result[index] = vi);
                c = c0 | c1;
                index += 1;
            }

            let (vn, c0) = ne_index!(x[index]).overflowing_sub(ne_index!(y[index]));
            let (vn, c1) = vn.overflowing_sub(c as $u);
            ne_index!(result[index] = vn);

            (result, c0 | c1)
        }

        /// Const implementation of `wrapping_sub` a small number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 128-bit subtraction (2x u128 + 2x u128), it optimizes to 1
        /// `sub` and 3 `sbb` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rcx, qword ptr [rsi]
        ///     mov     r8, qword ptr [rsi + 8]
        ///     sub     rcx, rdx
        ///     sbb     r8, 0
        ///     mov     rax, rdi
        ///     mov     rdx, qword ptr [rsi + 16]
        ///     sbb     rdx, 0
        ///     mov     rsi, qword ptr [rsi + 24]
        ///     sbb     rsi, 0
        ///     mov     qword ptr [rdi], rcx
        ///     mov     qword ptr [rdi + 8], r8
        ///     mov     qword ptr [rdi + 16], rdx
        ///     mov     qword ptr [rdi + 24], rsi
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_limb<const N: usize>(x: &[$u; N], y: $u) -> [$u; N] {
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let (mut v, mut c) = ne_index!(x[index]).overflowing_sub(y);
            ne_index!(result[index] = v);
            index += 1;
            while index < N - 1 {
                (v, c) = ne_index!(x[index]).overflowing_sub(c as $u);
                ne_index!(result[index] = v);
                index += 1;
            }

            v = ne_index!(x[index]).wrapping_sub(c as $u);
            ne_index!(result[index] = v);

            result
        }

        /// Const implementation to subtract a small number from the wider type.
        ///
        /// Returns the value and if the sub overflowed.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 128-bit subtraction (2x u128 + 2x u128), it optimizes to 1
        /// `sub`, 3 `sbb`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rcx, qword ptr [rsi]
        ///     mov     r8, qword ptr [rsi + 8]
        ///     sub     rcx, rdx
        ///     sbb     r8, 0
        ///     mov     rdx, qword ptr [rsi + 16]
        ///     sbb     rdx, 0
        ///     mov     rax, rdi
        ///     mov     rsi, qword ptr [rsi + 24]
        ///     sbb     rsi, 0
        ///     mov     qword ptr [rdi], rcx
        ///     mov     qword ptr [rdi + 8], r8
        ///     mov     qword ptr [rdi + 16], rdx
        ///     mov     qword ptr [rdi + 24], rsi
        ///     setb    byte ptr [rdi + 32]
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_limb<const N: usize>(x: &[$u; N], y: $u) -> ([$u; N], bool) {
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let (mut v, mut c) = ne_index!(x[index]).overflowing_sub(y);
            ne_index!(result[index] = v);
            index += 1;
            while index < N - 1 {
                (v, c) = ne_index!(x[index]).overflowing_sub(c as $u);
                ne_index!(result[index] = v);
                index += 1;
            }

            (v, c) = ne_index!(x[index]).overflowing_sub(c as $u);
            ne_index!(result[index] = v);

            (result, c)
        }
    };
}

sub_unsigned_impl!(
    u32,
    wrapping_full => wrapping_sub_u32,
    overflowing_full => overflowing_sub_u32,
    wrapping_limb => wrapping_sub_limb_u32,
    overflowing_limb => overflowing_sub_limb_u32
);
sub_unsigned_impl!(
    u64,
    wrapping_full => wrapping_sub_u64,
    overflowing_full => overflowing_sub_u64,
    wrapping_limb => wrapping_sub_limb_u64,
    overflowing_limb => overflowing_sub_limb_u64
);

macro_rules! mul_unsigned_impl {
    (
        type =>
        $t:ty,wide =>
        $w:ty,wrapping_full =>
        $wrapping_full:ident,wrapping_limb =>
        $wrapping_limb:ident,overflowing_full =>
        $overflowing_full:ident,overflowing_limb =>
        $overflowing_limb:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_mul` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow. This allows the two arrays
        /// to be different sizes so we can use the same algorithm when multiplying
        /// by a small factor, such as multiplying a [`u256`][crate::u256] by a
        /// `u64`, while having major optimizations.
        ///
        /// This uses long multiplication of smaller limbs, which has significantly
        /// better performance than an algorithm with a simulated [`mulx`] approach.
        ///
        /// Returns the low and high bits, in that order.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline(always)]
        pub const fn $wrapping_full<const M: usize, const N: usize>(
            x: &[$t; M],
            y: &[$t; N],
        ) -> [$t; M] {
            // NOTE: This assumes our multiplier is at least the multiplicand
            // dimensions, so we can just invert it in the other case.
            assert!(M >= N, "lhs must be >= than rhs");

            const SHIFT: u32 = <$t>::BITS;
            let mut r: [$t; M] = [0; M];
            let mut carry: $t;

            // this is effectively an 2D matrix for long multiplication.
            let mut i: usize = 0;
            let mut j: usize;
            while i < M {
                carry = 0;
                j = 0;
                while j < N && i + j < M {
                    let ij = i + j;
                    // FIXME: Replace with `carrying_mul` when we add it
                    // NOTE: This is a major miscompilation for performance regression.
                    // Not having all of these statements on the same line somehow
                    // causes a performance regression, a serious one.
                    let prod = carry as $w
                        + ne_index!(r[ij]) as $w
                        + (ne_index!(x[i]) as $w) * (ne_index!(y[j]) as $w);
                    ne_index!(r[ij] = prod as $t);
                    carry = (prod >> SHIFT) as $t;
                    j += 1;
                }

                // If we have the same dimensions and we have a carry,
                // then we always have an overflow. Otherwise, if it's
                // less dimensions, then we might not. Carry the overflow
                // here. In the next loop this will be added back in.
                if N < M && i + N < M {
                    ne_index!(r[i + N] = carry);
                }
                i += 1;
            }

            r
        }

        /// Const implementation of `wrapping_mul` for internal algorithm use.
        #[inline(always)]
        pub const fn $wrapping_limb<const N: usize>(x: &[$t; N], y: $t) -> [$t; N] {
            $wrapping_full(&x, &[y])
        }

        /// Const implementation of `overflowing_mul` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow and if the result overflowed.
        /// This allows the two arrays to be different sizes so we can use the same
        /// algorithm when multiplying by a small factor, such as multiplying a
        /// [`u256`][crate::u256] by a `u64`, while having major optimizations.
        ///
        /// This uses long multiplication of smaller limbs, which has significantly
        /// better performance than an algorithm with a simulated [`mulx`] approach.
        ///
        /// Returns the low and high bits, in that order.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline(always)]
        pub const fn $overflowing_full<const M: usize, const N: usize>(
            x: &[$t; M],
            y: &[$t; N],
        ) -> ([$t; M], bool) {
            // NOTE: This assumes our multiplier is at least the multiplicand
            // dimensions, so we can just invert it in the other case.
            assert!(M >= N, "lhs must be >= than rhs");

            const SHIFT: u32 = <$t>::BITS;
            let mut r: [$t; M] = [0; M];
            let mut carry: $t;
            let mut overflowed = false;

            // this is effectively an 2D matrix for long multiplication.
            let mut i: usize = 0;
            let mut j: usize;
            while i < M {
                carry = 0;
                j = 0;
                // NOTE: This is likely due to a miscompilation but this
                // is significantly faster than indexing within the loop
                // on `x86_64`.
                let xi = ne_index!(x[i]);
                while j < N {
                    let ij = i + j;
                    let yj = ne_index!(y[j]);
                    if ij < M {
                        // FIXME: Replace with `carrying_mul` when we add it
                        // NOTE: This is a major miscompilation for performance regression.
                        // Not having all of these statements on the same line somehow
                        // causes a performance regression, a serious one.
                        let prod = carry as $w + ne_index!(r[ij]) as $w + (xi as $w) * (yj as $w);
                        ne_index!(r[ij] = prod as $t);
                        carry = (prod >> SHIFT) as $t;
                    } else if xi != 0 && yj != 0 {
                        overflowed = true;
                        break;
                    }
                    j += 1;
                }

                // If we have the same dimensions and we have a carry,
                // then we always have an overflow. Otherwise, if it's
                // less dimensions, then we might not. Carry the overflow
                // here. In the next loop this will be added back in.
                // Only if we've carried to the last digit have we overflowed.
                if N < M && i + N < M {
                    ne_index!(r[i + N] = carry);
                } else if carry != 0 {
                    overflowed = true;
                }
                i += 1;
            }

            (r, overflowed)
        }

        /// Const implementation of `overflowing_mul` for internal algorithm use.
        #[inline(always)]
        pub const fn $overflowing_limb<const N: usize>(x: &[$t; N], y: $t) -> ([$t; N], bool) {
            $overflowing_full(&x, &[y])
        }
    };
}

mul_unsigned_impl!(
    type => u32,
    wide => u64,
    wrapping_full => wrapping_mul_u32,
    wrapping_limb => wrapping_mul_limb_u32,
    overflowing_full => overflowing_mul_u32,
    overflowing_limb => overflowing_mul_limb_u32,
);
mul_unsigned_impl!(
    type => u64,
    wide => u128,
    wrapping_full => wrapping_mul_u64,
    wrapping_limb => wrapping_mul_limb_u64,
    overflowing_full => overflowing_mul_u64,
    overflowing_limb => overflowing_mul_limb_u64,
);

macro_rules! shift_unsigned_impl {
    ($($u:ty => $shl:ident, $shr:ident,)*) => ($(
        /// Const implementation of `Shl` for internal algorithm use.
        ///
        /// # Design & Assembly
        ///
        /// There were 3 different variants attempted, of which the
        /// 1st had the best performance for `u128` but the 3rd had
        /// the best for `u64` and smaller. However, the performance
        /// for each was practically identical.
        ///
        /// All 3 have identical ASM for the 1st branch generated,
        /// just as expected, if the shift is larger than the number
        /// of bits. The 1st then speculatively jumps on zero, which
        /// branch prediction will likely almost always skip this
        /// jump (since shift-by-zero is unlikely to occur.) The
        /// 3rd replaces all but the first jump wit `cmove`, but
        /// since branch prediction is excellent here likely hurts
        /// overall performance. The 2nd case is the worst of both
        /// worlds: it keeps the same number of jumps and cmoves,
        /// but jumps after all the cmoves have been executed, which
        /// would have very detrimental performance for shifts by 0.
        ///
        /// ## Branch on Zero (1st Algorithm)
        ///
        /// ```rust,ignore
        /// if shift >= BITS {
        ///     (0, x0.wrapping_shl(shift - BITS))
        /// } else if shift == 0 {
        ///     (x0, x1)
        /// } else {
        ///     let hi = x1.wrapping_shl(shift);
        ///     let lo = x0.wrapping_shl(shift);
        ///     let carry = x0.wrapping_shr(BITS - shift);
        ///     (lo, hi | carry)
        /// }
        /// ```
        ///
        /// ## Full Branch on Carry (2nd Algorithm)
        ///
        /// ```rust, ignore
        /// if shift >= BITS {
        ///     (0, x0.wrapping_shl(shift - BITS))
        /// } else {
        ///     let hi = x1.wrapping_shl(shift);
        ///     let lo = x0.wrapping_shl(shift);
        ///     let is_zero = shift == 0;
        ///     match x0.checked_shr(BITS - shift) {
        ///         Some(carry) => (lo, hi | carry),
        ///         None => (lo, hi),
        ///     }
        /// }
        /// ```
        ///
        /// ## Get Carry via Branch (3rd Algorithm)
        ///
        /// ```rust, ignore
        /// if shift >= BITS {
        ///     (0, x0.wrapping_shl(shift - BITS))
        /// } else {
        ///     let hi = x1.wrapping_shl(shift);
        ///     let lo = x0.wrapping_shl(shift);
        ///     let is_zero = shift == 0;
        ///     let carry = match x0.checked_shr(BITS - shift) {
        ///         Some(carry) => carry,
        ///         None => 0,
        ///     };
        ///     (lo, hi | carry)
        /// }
        /// ```
        #[inline]
        pub const fn $shl<const N: usize>(x: [$u; N], shift: u32) -> [$u; N] {
            assert!(N >= 2, "must have at least 2 limbs");
            const BITS: u32 = <$u>::BITS;
            debug_assert!(shift < N as u32 * BITS, "attempt to shift left with overflow");
            let limb_n = shift as usize >> BITS.trailing_zeros();
            let bits_n = shift & (BITS - 1);
            let inv_n = BITS - bits_n;

            let mut result = [0; N];
            if N == 2 {
                // Simple case, only have to worry about swapping bits, no digits.
                let x0 = ne_index!(x[0]);
                let x1 = ne_index!(x[1]);
                let (r0, r1) = if limb_n != 0 {
                    (0, x0 << bits_n)
                } else if shift == 0 {
                    (x0, x1)
                } else {
                    // NOTE: We have `0xABCD_EFGH`, and we want to shift by 1,
                    // so to `0xBCDE_FGH0`, or we need to carry the `D`. So,
                    // our mask needs to be `0x000X`, or `0xXXXX >> (4 - 1)`,
                    // and then the value needs to be shifted left `<< (4 - 1)`.
                    let hi = x1 << bits_n;
                    let lo = x0 << bits_n;
                    let carry = x0 >> inv_n;
                    (lo, hi | carry)
                };
                ne_index!(result[0] = r0);
                ne_index!(result[1] = r1);
            } else if bits_n != 0 {
                // need to shift first our limbs and bits within each limb
                // for example, a limb shift of 2 zeros out the right 2 limbs,
                // and then processes the remaining limb.
                let mut index = limb_n;
                let mut carry = 0;
                while index < N {
                    let xi = ne_index!(x[index - limb_n]);
                    ne_index!(result[index] = (xi << bits_n) | carry);
                    carry = xi >> inv_n;
                    index += 1;
                }
            } else {
                // no bit shift, just limb shifts
                let mut index = limb_n;
                while index < N {
                    let xi = ne_index!(x[index - limb_n]);
                    ne_index!(result[index] = xi);
                    index += 1;
                }
            }

            result
        }

        /// Const implementation of `Shr` for internal algorithm use.
        ///
        /// # Design & Assembly
        ///
        /// There were 3 different variants attempted, of which the
        /// 1st had the best performance for `u128` but the 3rd had
        /// the best for `u64` and smaller. However, the performance
        /// for each was practically identical.
        ///
        /// All 3 have identical ASM for the 1st branch generated,
        /// just as expected, if the shift is larger than the number
        /// of bits. The 1st then speculatively jumps on zero, which
        /// branch prediction will likely almost always skip this
        /// jump (since shift-by-zero is unlikely to occur.) The
        /// 3rd replaces all but the first jump wit `cmove`, but
        /// since branch prediction is excellent here likely hurts
        /// overall performance. The 2nd case is the worst of both
        /// worlds: it keeps the same number of jumps and cmoves,
        /// but jumps after all the cmoves have been executed, which
        /// would have very detrimental performance for shifts by 0.
        ///
        /// ## Branch on Zero (1st Algorithm)
        ///
        /// ```rust,ignore
        /// if shift >= BITS {
        ///     (0, x0.wrapping_shr(shift - BITS))
        /// } else if shift == 0 {
        ///     (x0, x1)
        /// } else {
        ///     let hi = x1.wrapping_shr(shift);
        ///     let lo = x0.wrapping_shr(shift);
        ///     let carry = x0.wrapping_shl(BITS - shift);
        ///     (lo, hi | carry)
        /// }
        /// ```
        ///
        /// ## Full Branch on Carry (2nd Algorithm)
        ///
        /// ```rust, ignore
        /// if shift >= BITS {
        ///     (0, x0.wrapping_shr(shift - BITS))
        /// } else {
        ///     let hi = x1.wrapping_shr(shift);
        ///     let lo = x0.wrapping_shr(shift);
        ///     let is_zero = shift == 0;
        ///     match x0.checked_shl(BITS - shift) {
        ///         Some(carry) => (lo, hi | carry),
        ///         None => (lo, hi),
        ///     }
        /// }
        /// ```
        ///
        /// ## Get Carry via Branch (3rd Algorithm)
        ///
        /// ```rust, ignore
        /// if shift >= BITS {
        ///     (0, x0.wrapping_shr(shift - BITS))
        /// } else {
        ///     let hi = x1.wrapping_shr(shift);
        ///     let lo = x0.wrapping_shr(shift);
        ///     let is_zero = shift == 0;
        ///     let carry = match x0.checked_shl(BITS - shift) {
        ///         Some(carry) => carry,
        ///         None => 0,
        ///     };
        ///     (lo, hi | carry)
        /// }
        /// ```
        #[inline]
        pub const fn $shr<const N: usize>(x: [$u; N], shift: u32) -> [$u; N] {
            assert!(N >= 2, "must have at least 2 limbs");
            const BITS: u32 = <$u>::BITS;
            debug_assert!(shift < N as u32 * BITS, "attempt to shift right with overflow");
            let limb_n = shift as usize >> BITS.trailing_zeros();
            let bits_n = shift & (BITS - 1);
            let inv_n = BITS - bits_n;

            let mut result = [0; N];
            if N == 2 {
                // Simple case, only have to worry about swapping bits, no digits.
                let x0 = ne_index!(x[0]);
                let x1 = ne_index!(x[1]);
                let (r0, r1) = if limb_n != 0 {
                    (x1 >> bits_n, 0)
                } else if bits_n == 0 {
                    (x0, x1)
                } else {
                    // NOTE: We have `0xABCD_EFGH`, and we want to shift by 1,
                    // so to `0x0ABC_DEFG`, or we need to carry the `D`. So,
                    // our mask needs to be `0x000X`, or `0xXXXX >> (4 - 1)`,
                    // and then the value needs to be shifted left `<< (4 - 1)`.
                    let hi = x1 >> bits_n;
                    let lo = x0 >> bits_n;
                    let carry = x1 << inv_n;
                    (lo | carry, hi)
                };
                ne_index!(result[0] = r0);
                ne_index!(result[1] = r1);
            } else if bits_n != 0 {
                // need to shift first our limbs and bits within each limb
                // for example, a limb shift of 2 zeros out the left 2 limbs,
                // and then processes the remaining limb.
                let mut index = N;
                let mut carry = 0;
                while index > limb_n {
                    index -= 1;
                    let xi = ne_index!(x[index]);
                    ne_index!(result[index - limb_n] = (xi >> bits_n) | carry);
                    carry = xi << inv_n;
                }
            } else {
                // no bit shift, just limb shifts
                let mut index = N;
                while index > limb_n {
                    index -= 1;
                    let xi = ne_index!(x[index]);
                    ne_index!(result[index - limb_n] = xi);
                }
            }

            result
        }
    )*);
}

shift_unsigned_impl! {
    u32 => shl_u32, shr_u32,
    u64 => shl_u64, shr_u64,
    u128 => shl_u128, shr_u128,
}

// UNARY OPS - UNSIGNED
// --------------------

macro_rules! rotate_unsigned_impl {
    ($($u:ty => $left:ident, $right:ident,)*) => ($(
        /// Shifts the bits to the left by a specified amount, `n`,
        /// wrapping the truncated bits to the end of the resulting integer.
        ///
        /// Please note this isn't the same operation as the `<<` shifting operator!
        ///
        /// # Assembly
        ///
        /// This is basically identical to the unsigned variant. It first
        /// conditionally swaps the low and high digits, jumps on zero,
        /// then performs 4 shifts and 2 ors to get the final results.
        ///
        /// ```asm
        /// rotate_left:
        ///     mov     r8d, edi
        ///     shr     r8d, 16
        ///     test    sil, 16
        ///     mov     eax, edi
        ///     cmove   eax, r8d
        ///     cmove   r8d, edi
        ///     mov     edx, esi
        ///     and     edx, 15
        ///     je      .LBB
        ///     mov     edi, eax
        ///     mov     ecx, edx
        ///     shl     edi, cl
        ///     movzx   r9d, ax
        ///     movzx   eax, r8w
        ///     neg     sil
        ///     and     sil, 15
        ///     mov     ecx, esi
        ///     shr     eax, cl
        ///     mov     ecx, edx
        ///     shl     r8d, cl
        ///     mov     ecx, esi
        ///     shr     r9d, cl
        ///     or      eax, edi
        ///     or      r9d, r8d
        ///     mov     r8d, r9d
        /// .LBB:
        ///     movzx   ecx, r8w
        ///     shl     eax, 16
        ///     or      eax, ecx
        ///     ret
        /// ```
        ///
        /// Note that `x86` supports the [`shld`] and [`shrd`] instructions,
        /// which make this way faster done as 128-bit integers than smaller
        /// types, so we prefer using the wide types when available.
        ///
        /// [`shld`]: https://www.felixcloutier.com/x86/shld
        /// [`shrd`]: https://www.felixcloutier.com/x86/shrd
        #[inline]
        pub const fn $left<const N: usize>(x: [$u; N], n: u32) -> [$u; N] {
            assert!(N >= 2, "must have at least 2 limbs");
            // 0bXYFFFF -> 0bFFFFXY
            const BITS: u32 = <$u>::BITS;
            // First, 0 out all bits above as if we did a narrowing case.
            // Then, we want to get `n` as a narrow cast for `log2(BITS)`,
            // then see if we have any upper digits. This optimizes it
            // with these bit tricks over the regular approach on `x86_64`.
            // Say. we if `u16`, then we'd first 0 out above `001F`.
            // Then, if we have `0x10` set, then we have to swap `(lo, hi)`.
            // Then we can just shift on `0xF`.
            //
            // This isn't great but a better than some naive approaches.
            let n = n % (N as u32 * BITS);
            let limb_n = (n >> BITS.trailing_zeros()) as usize;
            let bits_n = n & (BITS - 1);
            let inv_n = BITS - bits_n;

            let mut result = [0; N];
            if N == 2 {
                // Simple case, only have to worry about swapping bits, at most swap 1 limb.
                let (x0, x1) = if limb_n != 0 {
                    (ne_index!(x[1]), ne_index!(x[0]))
                } else {
                    (ne_index!(x[0]), ne_index!(x[1]))
                };
                let (r0, r1) = if bits_n == 0 {
                    (x0, x1)
                } else {
                    let hi = (x1 << bits_n) | (x0 >> BITS - bits_n);
                    let lo = (x0 << bits_n) | (x1 >> BITS - bits_n);
                    (lo, hi)
                };
                ne_index!(result[0] = r0);
                ne_index!(result[1] = r1);
            } else if bits_n != 0 {
                let mut index = 0;
                let mut carry = 0;
                while index < N {
                    let rot_n = (index + limb_n) % N;
                    let xi = ne_index!(x[index]);
                    let ri = (xi << bits_n) | carry;
                    carry = xi >> inv_n;
                    ne_index!(result[rot_n] = ri);
                    index += 1;
                }
                ne_index!(result[limb_n] = ne_index!(result[limb_n]) | carry);
            } else {
                // no bit shift, just limb shifts
                let mut index = 0;
                while index < N {
                    let rot_n = (index + limb_n) % N;
                    let xi = ne_index!(x[index]);
                    ne_index!(result[rot_n] = xi);
                    index += 1;
                }
            }

            result
        }

        /// Shifts the bits to the right by a specified amount, `n`,
        /// wrapping the truncated bits to the beginning of the resulting
        /// integer.
        ///
        /// Please note this isn't the same operation as the `>>` shifting operator!
        ///
        /// Note that `x86` supports the [`shld`] and [`shrd`] instructions,
        /// which make this way faster done as 128-bit integers than smaller
        /// types, so we prefer using the wide types when available.
        ///
        /// [`shld`]: https://www.felixcloutier.com/x86/shld
        /// [`shrd`]: https://www.felixcloutier.com/x86/shrd
        #[inline]
        pub const fn $right<const N: usize>(x: [$u; N], n: u32) -> [$u; N] {
            assert!(N >= 2, "must have at least 2 limbs");
            // See rotate_left for the description
            // 0bFFFFXY -> 0bXYFFFF
            const BITS: u32 = <$u>::BITS;
            let n = n % (N as u32 * BITS);
            let limb_n = (n >> BITS.trailing_zeros()) as usize;
            let bits_n = n & (BITS - 1);
            let inv_n = BITS - bits_n;

            let mut result = [0; N];
            if N ==  2 {
                // Simple case, only have to worry about swapping bits, at most swap 1 limb.
                let (x0, x1) = if limb_n != 0 {
                    (ne_index!(x[1]), ne_index!(x[0]))
                } else {
                    (ne_index!(x[0]), ne_index!(x[1]))
                };
                let (r0, r1) = if bits_n == 0 {
                    (x0, x1)
                } else {
                    let hi = (x1 >> bits_n) | (x0 << BITS - bits_n);
                    let lo = (x0 >> bits_n) | (x1 << BITS - bits_n);
                    (lo, hi)
                };
                ne_index!(result[0] = r0);
                ne_index!(result[1] = r1);
            } else if bits_n != 0 {
                let mut index = 0;
                let mut carry = 0;
                while index < N {
                    let rot_n = (index + limb_n) % N;
                    let xi = ne_index!(x[rot_n]);
                    let ri = (xi >> bits_n) | carry;
                    carry = xi << inv_n;
                    ne_index!(result[index] = ri);
                    index += 1;
                }
                ne_index!(result[0] = ne_index!(result[0]) | carry);
            } else {
                // no bit shift, just limb shifts
                let mut index = 0;
                while index < N {
                    let rot_n = (index + limb_n) % N;
                    let xi = ne_index!(x[rot_n]);
                    ne_index!(result[index] = xi);
                    index += 1;
                }
            }

            result
        }
    )*);
}

rotate_unsigned_impl! {
    u32 => rotate_left_u32, rotate_right_u32,
    u64 => rotate_left_u64, rotate_right_u64,
    u128 => rotate_left_u128, rotate_right_u128,
}

// BINARY OPS - SIGNED
// -------------------

macro_rules! add_signed_impl {
    (
        $u:ty,
        $s:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_ulimb =>
        $wrapping_ulimb:ident,overflowing_ulimb =>
        $overflowing_ulimb:ident,wrapping_ilimb =>
        $wrapping_ilimb:ident,overflowing_ilimb =>
        $overflowing_ilimb:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_add` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 256-bit addition (4x u64 + 4x u64), it optimizes to 1
        /// `add` and 3 `adc` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     mov     rcx, qword ptr [rsi]
        ///     mov     rdi, qword ptr [rsi + 8]
        ///     add     rcx, qword ptr [rdx]
        ///     mov     r8, qword ptr [rsi + 16]
        ///     adc     rdi, qword ptr [rdx + 8]
        ///     mov     r9, qword ptr [rdx + 24]
        ///     adc     r8, qword ptr [rdx + 16]
        ///     adc     r9, qword ptr [rsi + 24]
        ///     mov     qword ptr [rax], rcx
        ///     mov     qword ptr [rax + 8], rdi
        ///     mov     qword ptr [rax + 16], r8
        ///     mov     qword ptr [rax + 24], r9
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_full<const N: usize>(x: &[$u; N], y: &[$u; N]) -> [$u; N] {
            // FIXME: Move to `carrying_add` once stable.
            assert!(<$u>::BITS == <$s>::BITS);
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            while index < N - 1 {
                let (vi, c0) = ne_index!(x[index]).overflowing_add(ne_index!(y[index]));
                let (vi, c1) = vi.overflowing_add(c as $u);
                ne_index!(result[index] = vi);
                c = c0 | c1;
                index += 1;
            }

            // NOTE: This is the same signed or unsigned.
            let vn = ne_index!(x[index]).wrapping_add(ne_index!(y[index]));
            ne_index!(result[index] = vn.wrapping_add(c as $u));

            result
        }

        /// Const implementation of `overflowing_add` for internal algorithm use.
        ///
        /// Returns the value and if the add overflowed. In practice,
        /// the nightly (carrying) and the overflowing add variants
        /// have the same ASM generated, but this might not be the
        /// case in the future or for different architectures.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 2
        /// `add`, 3 `adc`, 2 `set` and 1 `xor` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rcx, qword ptr [rsi + 24]
        ///     add     rcx, qword ptr [rdx + 24]
        ///     mov     r8, qword ptr [rsi]
        ///     seto    r9b
        ///     add     r8, qword ptr [rdx]
        ///     mov     r10, qword ptr [rsi + 8]
        ///     adc     r10, qword ptr [rdx + 8]
        ///     mov     rsi, qword ptr [rsi + 16]
        ///     adc     rsi, qword ptr [rdx + 16]
        ///     mov     rax, rdi
        ///     adc     rcx, 0
        ///     seto    dl
        ///     xor     dl, r9b
        ///     mov     qword ptr [rdi], r8
        ///     mov     qword ptr [rdi + 8], r10
        ///     mov     qword ptr [rdi + 16], rsi
        ///     mov     qword ptr [rdi + 24], rcx
        ///     mov     byte ptr [rdi + 32], dl
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_full<const N: usize>(
            x: &[$u; N],
            y: &[$u; N],
        ) -> ([$u; N], bool) {
            // FIXME: Move to `carrying_add` once stable.
            assert!(<$u>::BITS == <$s>::BITS);
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            while index < N - 1 {
                let (vi, c0) = ne_index!(x[index]).overflowing_add(ne_index!(y[index]));
                let (vi, c1) = vi.overflowing_add(c as $u);
                ne_index!(result[index] = vi);
                c = c0 | c1;
                index += 1;
            }

            // NOTE: There's a **VERY** specific edge-case where we can
            // have overflow but no overflow occurred:
            // 1. We have an overflow in our lo borrowing sub.
            // 2. We "overflow" in our hi borrowing sub exactly to `MAX`
            // 3. We then add 1 and overflow to `MIN`.
            //
            // In short, we have `-1 + MIN + 1`, as a case, and we wrap to
            // `MAX`, which then wraps back to `MIN`, exactly what we
            // needed.

            // NOTE: We need to do this as a **SIGNED** operation.
            let xn = ne_index!(x[index]) as $s;
            let yn = ne_index!(y[index]) as $s;
            let (vn, c0) = xn.overflowing_add(yn);
            let (vn, c1) = vn.overflowing_add(c as $s);
            ne_index!(result[index] = vn as $u);

            // `c == 0`, then `c1 == 0`, so always want `c1`
            // `c == 1`, then only want `c0` or `c1`, not both
            (result, c0 ^ c1)
        }

        /// Const implementation to add a small, unsigned number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// # Assembly
        ///
        /// This optimizes fairly well, for example, on `x86_64`,
        /// for a 256-bit addition (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `add` and 3 `adc` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     mov     rcx, qword ptr [rsi + 8]
        ///     mov     rdi, qword ptr [rsi + 16]
        ///     add     rdx, qword ptr [rsi]
        ///     adc     rcx, 0
        ///     adc     rdi, 0
        ///     mov     rsi, qword ptr [rsi + 24]
        ///     adc     rsi, 0
        ///     mov     qword ptr [rax], rdx
        ///     mov     qword ptr [rax + 8], rcx
        ///     mov     qword ptr [rax + 16], rdi
        ///     mov     qword ptr [rax + 24], rsi
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_ulimb<const N: usize>(x: &[$u; N], y: $u) -> [$u; N] {
            assert!(N >= 2);
            assert!(<$u>::BITS == <$s>::BITS);

            let mut index = 0;
            let mut result = [0; N];
            let (mut v, mut c) = ne_index!(x[index]).overflowing_add(y);
            ne_index!(result[index] = v);
            index += 1;
            while index < N - 1 {
                (v, c) = ne_index!(x[index]).overflowing_add(c as $u);
                ne_index!(result[index] = v);
                index += 1;
            }

            // NOTE: This has the same results as signed or unsigned.
            v = ne_index!(x[index]).wrapping_add(c as $u);
            ne_index!(result[index] = v);

            result
        }

        /// Const implementation to add a small, unsigned number to the wider type.
        ///
        /// Returns the value and if the add overflowed.
        ///
        /// # Assembly
        ///
        /// This optimizes fairly well, for example, on `x86_64`,
        /// for a 256-bit addition (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `add`, 3 `adc`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     add     rdx, qword ptr [rsi]
        ///     mov     rcx, qword ptr [rsi + 8]
        ///     mov     r8, qword ptr [rsi + 16]
        ///     adc     rcx, 0
        ///     adc     r8, 0
        ///     mov     rax, rdi
        ///     mov     rsi, qword ptr [rsi + 24]
        ///     adc     rsi, 0
        ///     mov     qword ptr [rdi], rdx
        ///     mov     qword ptr [rdi + 8], rcx
        ///     mov     qword ptr [rdi + 16], r8
        ///     mov     qword ptr [rdi + 24], rsi
        ///     seto    byte ptr [rdi + 32]
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_ulimb<const N: usize>(x: &[$u; N], y: $u) -> ([$u; N], bool) {
            assert!(N >= 2);
            assert!(<$u>::BITS == <$s>::BITS);

            let mut index = 0;
            let mut result = [0; N];
            let (mut v, mut c) = ne_index!(x[index]).overflowing_add(y);
            ne_index!(result[index] = v);
            index += 1;
            while index < N - 1 {
                (v, c) = ne_index!(x[index]).overflowing_add(c as $u);
                ne_index!(result[index] = v);
                index += 1;
            }

            let xn = ne_index!(x[index]) as $s;
            let (v, c) = xn.overflowing_add(c as $s);
            ne_index!(result[index] = v as $u);

            (result, c)
        }

        /// Const implementation to add a small, signed number to the wider type.
        ///
        /// Returns the value, wrapping on overflow. This is effectively the
        /// implementation of the wider type, just with an extra bitshift to expand
        /// the type to the wider width.
        ///
        /// # Assembly
        ///
        /// This optimizes well, for example, on `x86_64`,
        /// for a 256-bit addition (1x u128, 1x i128 + 1x i64), it
        /// optimizes to 1 `add`, 3 `adc`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     mov     rcx, rdx
        ///     sar     rcx, 63
        ///     mov     rdi, qword ptr [rsi + 8]
        ///     mov     r8, qword ptr [rsi + 16]
        ///     add     rdx, qword ptr [rsi]
        ///     adc     rdi, 0
        ///     adc     r8, 0
        ///     adc     rcx, qword ptr [rsi + 24]
        ///     mov     qword ptr [rax], rdx
        ///     mov     qword ptr [rax + 8], rdi
        ///     mov     qword ptr [rax + 16], r8
        ///     mov     qword ptr [rax + 24], rcx
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_ilimb<const N: usize>(x: &[$u; N], y: $s) -> [$u; N] {
            // NOTE: We just want to set it as the low bits of `y` and the single high bit.
            let sign_bit = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let mut rhs = [sign_bit; N];
            ne_index!(rhs[0] = y as $u);
            $wrapping_full(x, &rhs)
        }

        /// Const implementation to add a small, signed number to the wider type.
        ///
        /// Returns the value and if the add overflowed. This is effectively the
        /// implementation of the wider type, just with an extra bitshift to expand
        /// the type to the wider width.
        ///
        /// # Assembly
        ///
        /// This optimizes well, for example, on `x86_64`, for a 256-bit addition
        /// (1x u128, 1x i128 + 1x i128), it optimizes to 2 `add`, 3 `adc`, 2 `set`,
        /// 1 `xor`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     mov     rcx, rdx
        ///     sar     rcx, 63
        ///     mov     rdi, qword ptr [rsi + 8]
        ///     mov     r8, qword ptr [rsi + 16]
        ///     add     rcx, qword ptr [rsi + 24]
        ///     seto    r9b
        ///     add     rdx, qword ptr [rsi]
        ///     adc     rdi, 0
        ///     adc     r8, 0
        ///     adc     rcx, 0
        ///     seto    sil
        ///     xor     sil, r9b
        ///     mov     qword ptr [rax], rdx
        ///     mov     qword ptr [rax + 8], rdi
        ///     mov     qword ptr [rax + 16], r8
        ///     mov     qword ptr [rax + 24], rcx
        ///     mov     byte ptr [rax + 32], sil
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_ilimb<const N: usize>(x: &[$u; N], y: $s) -> ([$u; N], bool) {
            // NOTE: We just want to set it as the low bits of `y` and the single high bit.
            let sign_bit = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let mut rhs = [sign_bit; N];
            ne_index!(rhs[0] = y as $u);
            $overflowing_full(x, &rhs)
        }
    };
}

add_signed_impl!(
    u32,
    i32,
    wrapping_full => wrapping_add_i32,
    overflowing_full => overflowing_add_i32,
    wrapping_ulimb => wrapping_add_ulimb_i32,
    overflowing_ulimb => overflowing_add_ulimb_i32,
    wrapping_ilimb => wrapping_add_ilimb_i32,
    overflowing_ilimb => overflowing_add_ilimb_i32
);
add_signed_impl!(
    u64,
    i64,
    wrapping_full => wrapping_add_i64,
    overflowing_full => overflowing_add_i64,
    wrapping_ulimb => wrapping_add_ulimb_i64,
    overflowing_ulimb => overflowing_add_ulimb_i64,
    wrapping_ilimb => wrapping_add_ilimb_i64,
    overflowing_ilimb => overflowing_add_ilimb_i64
);

macro_rules! sub_signed_impl {
    (
        $u:ty,
        $s:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_ulimb =>
        $wrapping_ulimb:ident,overflowing_ulimb =>
        $overflowing_ulimb:ident,wrapping_ilimb =>
        $wrapping_ilimb:ident,overflowing_ilimb =>
        $overflowing_ilimb:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_sub` for internal algorithm use.
        ///
        /// Returns the value and if the sub underflowed.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on `x86_64`,
        /// for a 256-bit subtraction (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `sub` and 3 `sbb` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, rdi
        ///     mov     rcx, qword ptr [rsi + 16]
        ///     mov     rdi, qword ptr [rsi]
        ///     sub     rdi, qword ptr [rdx]
        ///     mov     r8, qword ptr [rsi + 8]
        ///     sbb     r8, qword ptr [rdx + 8]
        ///     sbb     rcx, qword ptr [rdx + 16]
        ///     mov     rsi, qword ptr [rsi + 24]
        ///     sbb     rsi, qword ptr [rdx + 24]
        ///     mov     qword ptr [rax], rdi
        ///     mov     qword ptr [rax + 8], r8
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], rsi
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_full<const N: usize>(x: &[$u; N], y: &[$u; N]) -> [$u; N] {
            // FIXME: Move to `borrowing_sub` once stable.
            assert!(<$u>::BITS == <$s>::BITS);
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            while index < N - 1 {
                let (vi, c0) = ne_index!(x[index]).overflowing_sub(ne_index!(y[index]));
                let (vi, c1) = vi.overflowing_sub(c as $u);
                ne_index!(result[index] = vi);
                c = c0 | c1;
                index += 1;
            }

            // NOTE: This is the same signed or unsigned.
            let vn = ne_index!(x[index]).wrapping_sub(ne_index!(y[index]));
            ne_index!(result[index] = vn.wrapping_sub(c as $u));

            result
        }

        /// Const implementation of `overflowing_sub` for internal algorithm use.
        ///
        /// Returns the value and if the sub underflowed.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit subtraction (2x u128 + 2x u128), it optimizes to 2
        /// `sub`, 3 `sbb`, 2 `set` and 1 `xor` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rcx, qword ptr [rsi + 24]
        ///     sub     rcx, qword ptr [rdx + 24]
        ///     mov     r8, qword ptr [rsi]
        ///     seto    r9b
        ///     sub     r8, qword ptr [rdx]
        ///     mov     r10, qword ptr [rsi + 8]
        ///     sbb     r10, qword ptr [rdx + 8]
        ///     mov     rsi, qword ptr [rsi + 16]
        ///     sbb     rsi, qword ptr [rdx + 16]
        ///     mov     rax, rdi
        ///     sbb     rcx, 0
        ///     seto    dl
        ///     xor     dl, r9b
        ///     mov     qword ptr [rdi], r8
        ///     mov     qword ptr [rdi + 8], r10
        ///     mov     qword ptr [rdi + 16], rsi
        ///     mov     qword ptr [rdi + 24], rcx
        ///     mov     byte ptr [rdi + 32], dl
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_full<const N: usize>(
            x: &[$u; N],
            y: &[$u; N],
        ) -> ([$u; N], bool) {
            // FIXME: Move to `borrowing_sub` once stable.
            assert!(<$u>::BITS == <$s>::BITS);
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            while index < N - 1 {
                let (vi, c0) = ne_index!(x[index]).overflowing_sub(ne_index!(y[index]));
                let (vi, c1) = vi.overflowing_sub(c as $u);
                ne_index!(result[index] = vi);
                c = c0 | c1;
                index += 1;
            }

            // NOTE: There's a **VERY** specific edge-case where we can
            // have overflow but no overflow occurred:
            // 1. We have an overflow in our lo borrowing sub.
            // 2. We "overflow" in our hi borrowing sub exactly to `MIN`
            // 3. We then subtract 1 and overflow to `MAX`.
            //
            // In short, we have `0 - MIN - 1`, as a case, and we wrap to
            // `MIN - 1`, which then wraps back to `MAX`, exactly what
            // we needed.

            // NOTE: We need to do this as a **SIGNED** operation.
            let xn = ne_index!(x[index]) as $s;
            let yn = ne_index!(y[index]) as $s;
            let (vn, c0) = xn.overflowing_sub(yn);
            let (vn, c1) = vn.overflowing_sub(c as $s);
            ne_index!(result[index] = vn as $u);

            // `c == 0`, then `c1 == 0`, so always want `c1`
            // `c == 1`, then only want `c0` or `c1`, not both
            (result, c0 ^ c1)
        }

        /// Const implementation to subtract a small, unsigned number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// # Assembly
        ///
        /// This optimizes fairly well, for example, on `x86_64`,
        /// for a 256-bit subtraction (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `sub` and 3 `sbb` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rcx, qword ptr [rsi]
        ///     mov     r8, qword ptr [rsi + 8]
        ///     sub     rcx, rdx
        ///     sbb     r8, 0
        ///     mov     rax, rdi
        ///     mov     rdx, qword ptr [rsi + 16]
        ///     sbb     rdx, 0
        ///     mov     rsi, qword ptr [rsi + 24]
        ///     sbb     rsi, 0
        ///     mov     qword ptr [rdi], rcx
        ///     mov     qword ptr [rdi + 8], r8
        ///     mov     qword ptr [rdi + 16], rdx
        ///     mov     qword ptr [rdi + 24], rsi
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_ulimb<const N: usize>(x: &[$u; N], y: $u) -> [$u; N] {
            assert!(N >= 2);
            assert!(<$u>::BITS == <$s>::BITS);

            let mut index = 0;
            let mut result = [0; N];
            let (mut v, mut c) = ne_index!(x[index]).overflowing_sub(y);
            ne_index!(result[index] = v);
            index += 1;
            while index < N - 1 {
                (v, c) = ne_index!(x[index]).overflowing_sub(c as $u);
                ne_index!(result[index] = v);
                index += 1;
            }

            // NOTE: This has the same results as signed or unsigned.
            v = ne_index!(x[index]).wrapping_sub(c as $u);
            ne_index!(result[index] = v);

            result
        }

        /// Const implementation to subtract a small, unsigned number to the wider type.
        ///
        /// Returns the value and if the subtract overflowed.
        ///
        /// # Assembly
        ///
        /// This optimizes fairly well, for example, on `x86_64`,
        /// for a 256-bit subtraction (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `sub`, 3 `sbb`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rcx, qword ptr [rsi]
        ///     mov     r8, qword ptr [rsi + 8]
        ///     sub     rcx, rdx
        ///     sbb     r8, 0
        ///     mov     rdx, qword ptr [rsi + 16]
        ///     sbb     rdx, 0
        ///     mov     rax, rdi
        ///     mov     rsi, qword ptr [rsi + 24]
        ///     sbb     rsi, 0
        ///     mov     qword ptr [rdi], rcx
        ///     mov     qword ptr [rdi + 8], r8
        ///     mov     qword ptr [rdi + 16], rdx
        ///     mov     qword ptr [rdi + 24], rsi
        ///     seto    byte ptr [rdi + 32]
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_ulimb<const N: usize>(x: &[$u; N], y: $u) -> ([$u; N], bool) {
            assert!(N >= 2);
            assert!(<$u>::BITS == <$s>::BITS);

            let mut index = 0;
            let mut result = [0; N];
            let (mut v, mut c) = ne_index!(x[index]).overflowing_sub(y);
            ne_index!(result[index] = v);
            index += 1;
            while index < N - 1 {
                (v, c) = ne_index!(x[index]).overflowing_sub(c as $u);
                ne_index!(result[index] = v);
                index += 1;
            }

            let xn = ne_index!(x[index]) as $s;
            let (v, c) = xn.overflowing_sub(c as $s);
            ne_index!(result[index] = v as $u);

            (result, c)
        }

        /// Const implementation to subtract a small, unsigned number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// # Assembly
        ///
        /// This optimizes well, for example, on `x86_64`,
        /// for a 256-bit subtraction (1x u128, 1x i128 + 1x i64), it
        /// optimizes to 1 `add`, 1 `sub`, 3 `sbb`, and 1 `shr`
        /// instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rcx, rdx
        ///     shr     rcx, 63
        ///     mov     r8, qword ptr [rsi + 16]
        ///     mov     r9, qword ptr [rsi]
        ///     mov     r10, qword ptr [rsi + 8]
        ///     add     rcx, qword ptr [rsi + 24]
        ///     sub     r9, rdx
        ///     sbb     r10, 0
        ///     sbb     r8, 0
        ///     mov     rax, rdi
        ///     sbb     rcx, 0
        ///     mov     qword ptr [rdi], r9
        ///     mov     qword ptr [rdi + 8], r10
        ///     mov     qword ptr [rdi + 16], r8
        ///     mov     qword ptr [rdi + 24], rcx
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_ilimb<const N: usize>(x: &[$u; N], y: $s) -> [$u; N] {
            // NOTE: We just want to set it as the low bits of `y` and the single high bit.
            let sign_bit = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let mut rhs = [sign_bit; N];
            ne_index!(rhs[0] = y as $u);
            $wrapping_full(x, &rhs)
        }

        /// Const implementation to subtract a small, signed number to the wider type.
        ///
        /// Returns the value and if the subtract overflowed.
        ///
        /// # Assembly
        ///
        /// This optimizes well, for example, on `x86_64`, for a 256-bit subtraction
        /// (1x u128, 1x i128 + 1x i128), it optimizes to 2 `sub`, 3 `sbb`, 2 `set`,
        /// 1 `xor`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     mov     rcx, rdx
        ///     sar     rcx, 63
        ///     mov     rdi, qword ptr [rsi + 16]
        ///     mov     r8, qword ptr [rsi]
        ///     mov     r9, qword ptr [rsi + 8]
        ///     mov     rsi, qword ptr [rsi + 24]
        ///     sub     rsi, rcx
        ///     seto    r10b
        ///     sub     r8, rdx
        ///     sbb     r9, rcx
        ///     sbb     rdi, rcx
        ///     sbb     rsi, 0
        ///     seto    cl
        ///     xor     cl, r10b
        ///     mov     qword ptr [rax], r8
        ///     mov     qword ptr [rax + 8], r9
        ///     mov     qword ptr [rax + 16], rdi
        ///     mov     qword ptr [rax + 24], rsi
        ///     mov     byte ptr [rax + 32], cl
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_ilimb<const N: usize>(x: &[$u; N], y: $s) -> ([$u; N], bool) {
            // NOTE: We just want to set it as the low bits of `y` and the single high bit.
            let sign_bit = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let mut rhs = [sign_bit; N];
            ne_index!(rhs[0] = y as $u);
            $overflowing_full(x, &rhs)
        }
    };
}

sub_signed_impl!(
    u32,
    i32,
    wrapping_full => wrapping_sub_i32,
    overflowing_full => overflowing_sub_i32,
    wrapping_ulimb => wrapping_sub_ulimb_i32,
    overflowing_ulimb => overflowing_sub_ulimb_i32,
    wrapping_ilimb => wrapping_sub_ilimb_i32,
    overflowing_ilimb => overflowing_sub_ilimb_i32
);
sub_signed_impl!(
    u64,
    i64,
    wrapping_full => wrapping_sub_i64,
    overflowing_full => overflowing_sub_i64,
    wrapping_ulimb => wrapping_sub_ulimb_i64,
    overflowing_ulimb => overflowing_sub_ulimb_i64,
    wrapping_ilimb => wrapping_sub_ilimb_i64,
    overflowing_ilimb => overflowing_sub_ilimb_i64
);

macro_rules! mul_signed_impl {
    (
        unsigned =>
        $u:ty,signed =>
        $s:ty,wrapping_unsigned =>
        $wrapping_unsigned:ident,wrapping_full =>
        $wrapping_full:ident,wrapping_ulimb =>
        $wrapping_ulimb:ident,wrapping_ilimb =>
        $wrapping_ilimb:ident,overflowing_unsigned =>
        $overflowing_unsigned:ident,overflowing_full =>
        $overflowing_full:ident,overflowing_ulimb =>
        $overflowing_ulimb:ident,overflowing_ilimb =>
        $overflowing_ilimb:ident,
    ) => {
        /// Const implementation of `wrapping_mul` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// Many different algorithms were attempted, with a soft [`mulx`] approach (1),
        /// a flat, fixed-width long multiplication (2), and a short-circuiting long
        /// multiplication (3). Algorithm (3) had the best performance for 128-bit
        /// multiplication, however, algorithm (1) was better for smaller type sizes.
        ///
        /// This also optimized much better when multiplying by a single or a half-sized
        /// item: rather than using 4 limbs, if we're multiplying `(u128, i128) * u128`,
        /// we can use 2 limbs for the right operand, and for `(u128, i128) * u64`, only
        /// 1 limb.
        ///
        /// # Assembly
        ///
        /// For 256-bit multiplication, the results are fairly similar to the unsigned
        /// variant for algorithm (3), escape instead of having up to 10 `mul` and 15
        /// `add` instructions, it can have up to 11 `mul` and 19 `add` instructions.
        /// All the other optimization caveats are as described above.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $wrapping_full<const M: usize, const N: usize>(
            x: &[$u; M],
            y: &[$u; N],
        ) -> [$u; M] {
            // NOTE: I know this sounds incredible but it's really just this.
            // All the actual overflow, everything handling is done, internally.
            $wrapping_unsigned(x, y)
        }

        /// Const implementation of `wrapping_mul` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// Many different algorithms were attempted, with a soft [`mulx`] approach (1),
        /// a flat, fixed-width long multiplication (2), and a short-circuiting long
        /// multiplication (3). Algorithm (3) had the best performance for 128-bit
        /// multiplication, however, algorithm (1) was better for smaller type sizes.
        ///
        /// This also optimized much better when multiplying by a single or a half-sized
        /// item: rather than using 4 limbs, if we're multiplying `(u128, i128) * u128`,
        /// we can use 2 limbs for the right operand, and for `(u128, i128) * u64`, only
        /// 1 limb.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`u16`) which can add optimizations
        /// for scalar word processing.
        ///
        /// # Assembly
        ///
        /// For 256-bit multiplication, the results are fairly similar to the unsigned
        /// variant for algorithm (3), escape instead of having up to 4 `mul` and 3
        /// `add` instructions, it can have up to 5 `mul` and 7 `add` instructions.
        /// All the other optimization caveats are as described above.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline(always)]
        pub const fn $wrapping_ulimb<const N: usize>(x: &[$u; N], y: $u) -> [$u; N] {
            $wrapping_unsigned(&x, &[y])
        }

        /// Const implementation of `wrapping_mul` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// Many different algorithms were attempted, with a soft [`mulx`] approach (1),
        /// a flat, fixed-width long multiplication (2), and a short-circuiting long
        /// multiplication (3). Algorithm (3) had the best performance for 128-bit
        /// multiplication, however, algorithm (1) was better for smaller type sizes.
        ///
        /// This also optimized much better when multiplying by a single or a half-sized
        /// item: rather than using 4 limbs, if we're multiplying `(u128, i128) * u128`,
        /// we can use 2 limbs for the right operand, and for `(u128, i128) * u64`, only
        /// 1 limb.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`i16`) which can add optimizations
        /// for scalar word processing.
        ///
        /// # Assembly
        ///
        /// For 256-bit multiplication, the results are fairly similar to the unsigned
        /// variant for algorithm (3), escape instead of having up to 4 `mul` and 3
        /// `add` instructions, it can have up to 5 `mul` and 7 `add` instructions.
        /// All the other optimization caveats are as described above.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline(always)]
        pub const fn $wrapping_ilimb<const N: usize>(x: &[$u; N], y: $s) -> [$u; N] {
            // NOTE: This does not work like above, but there is a trick.
            // Widen the type and we can do the exact same approach.
            let sign_bit = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let mut rhs = [sign_bit; N];
            ne_index!(rhs[0] = y as $u);
            $wrapping_unsigned(&x, &rhs)
        }

        /// Const implementation of `overflowing_mul` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow and if the result overflowed.
        ///
        /// Many different algorithms were attempted, with a soft [`mulx`] approach (1),
        /// a flat, fixed-width long multiplication (2), and a short-circuiting long
        /// multiplication (3). Algorithm (3) had the best performance for 128-bit
        /// multiplication, however, algorithm (1) was better for smaller type sizes.
        ///
        /// This also optimized much better when multiplying by a single or a half-sized
        /// item: rather than using 4 limbs, if we're multiplying `(u128, i128) * u128`,
        /// we can use 2 limbs for the right operand, and for `(u128, i128) * u64`, only
        /// 1 limb.
        ///
        /// # Assembly
        ///
        /// The analysis here is practically identical to that of `wrapping_full`.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $overflowing_full<const M: usize, const N: usize>(
            x: &[$u; M],
            y: &[$u; N],
        ) -> ([$u; M], bool) {
            // general approach is unsigned multiplication, then convert
            // back to the signed variants by checking if both should be negative
            // this is **WAY** slower than our warpping variant, since we
            // need to handle wrapping, sign checks, etc., all which cause massive
            // performance overhead
            let x_is_negative = is_negative!(x, $s);
            let y_is_negative = is_negative!(y, $s);
            let should_be_negative = x_is_negative ^ y_is_negative;
            let x = if x_is_negative {
                negate!(x, M, $u)
            } else {
                *x
            };
            let y = if y_is_negative {
                negate!(y, N, $u)
            } else {
                *y
            };

            let (mut r, overflowed) = $overflowing_unsigned(&x, &y);
            let msl = ne_index!(r[M - 1]) as $s;
            let r_is_negative = msl < 0;
            if !should_be_negative {
                (r, overflowed | r_is_negative)
            } else {
                // convert our unsigned integer to 2's complement from an
                // abs value. if our value is exactly `::MIN`, then it didn't
                // wrap and it shouldn't be negative
                // NOTE: We want to negate this, which will always work since
                // `::MAX + 1` will wrap to min as expected.
                let is_min = msl == <$s>::MIN;
                r = negate!(r, M, $u);
                (r, overflowed | (r_is_negative ^ is_min))
            }
        }

        /// Const implementation of `overflowing_mul` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// Many different algorithms were attempted, with a soft [`mulx`] approach (1),
        /// a flat, fixed-width long multiplication (2), and a short-circuiting long
        /// multiplication (3). Algorithm (3) had the best performance for 128-bit
        /// multiplication, however, algorithm (1) was better for smaller type sizes.
        ///
        /// This also optimized much better when multiplying by a single or a half-sized
        /// item: rather than using 4 limbs, if we're multiplying `(u128, i128) * u128`,
        /// we can use 2 limbs for the right operand, and for `(u128, i128) * u64`, only
        /// 1 limb.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`u16`) which can add optimizations
        /// for scalar word processing.
        ///
        /// # Assembly
        ///
        /// The analysis here is practically identical to that of `wrapping_ulimb`.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline(always)]
        pub const fn $overflowing_ulimb<const N: usize>(x: &[$u; N], y: $u) -> ([$u; N], bool) {
            let mut rhs = [0; N];
            ne_index!(rhs[0] = y);
            $overflowing_full(&x, &rhs)
        }

        /// Const implementation of `overflowing_mul` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// Many different algorithms were attempted, with a soft [`mulx`] approach (1),
        /// a flat, fixed-width long multiplication (2), and a short-circuiting long
        /// multiplication (3). Algorithm (3) had the best performance for 128-bit
        /// multiplication, however, algorithm (1) was better for smaller type sizes.
        ///
        /// This also optimized much better when multiplying by a single or a half-sized
        /// item: rather than using 4 limbs, if we're multiplying `(u128, i128) * u128`,
        /// we can use 2 limbs for the right operand, and for `(u128, i128) * u64`, only
        /// 1 limb.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`u16`) which can add optimizations
        /// for scalar word processing.
        ///
        /// # Assembly
        ///
        /// The analysis here is practically identical to that of `wrapping_ilimb`.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline(always)]
        pub const fn $overflowing_ilimb<const N: usize>(x: &[$u; N], y: $s) -> ([$u; N], bool) {
            let sign_bit = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let mut rhs = [sign_bit; N];
            ne_index!(rhs[0] = y as $u);
            $overflowing_full(&x, &rhs)
        }
    };
}

mul_signed_impl!(
    unsigned => u32,
    signed => i32,
    wrapping_unsigned => wrapping_mul_u32,
    wrapping_full => wrapping_mul_i32,
    wrapping_ulimb => wrapping_mul_ulimb_i32,
    wrapping_ilimb => wrapping_mul_ilimb_i32,
    overflowing_unsigned => overflowing_mul_u32,
    overflowing_full => overflowing_mul_i32,
    overflowing_ulimb => overflowing_mul_ulimb_i32,
    overflowing_ilimb => overflowing_mul_ilimb_i32,
);
mul_signed_impl!(
    unsigned => u64,
    signed => i64,
    wrapping_unsigned => wrapping_mul_u64,
    wrapping_full => wrapping_mul_i64,
    wrapping_ulimb => wrapping_mul_ulimb_i64,
    wrapping_ilimb => wrapping_mul_ilimb_i64,
    overflowing_unsigned => overflowing_mul_u64,
    overflowing_full => overflowing_mul_i64,
    overflowing_ulimb => overflowing_mul_ulimb_i64,
    overflowing_ilimb => overflowing_mul_ilimb_i64,
);

macro_rules! shift_signed_impl {
    ($($u:ty, $s:ty => $shl:ident, $shr:ident,)*) => ($(
        /// Const implementation of `Shl` for internal algorithm use.
        ///
        /// Rust follows the C++20 semantics for this: `a << b` is equal to
        /// `a * 2^b`, which is quite easy to calculate. This result will
        /// wrap. For example, we can get the following:
        ///
        /// ```rust
        /// // From: 0b0000000000000001
        /// // To:   0b1000000000000000
        /// assert_eq!(1i16 << 15, i16::MIN);
        /// ```
        ///
        /// # Design & Assembly
        ///
        /// There were 3 different variants attempted, of which the
        /// 1st had the best performance for `u128` but the 3rd had
        /// the best for `u64` and smaller. However, the performance
        /// for each was practically identical.
        ///
        /// All 3 have identical ASM for the 1st branch generated,
        /// just as expected, if the shift is larger than the number
        /// of bits. The 1st then speculatively jumps on zero, which
        /// branch prediction will likely almost always skip this
        /// jump (since shift-by-zero is unlikely to occur.) The
        /// 3rd replaces all but the first jump wit `cmove`, but
        /// since branch prediction is excellent here likely hurts
        /// overall performance. The 2nd case is the worst of both
        /// worlds: it keeps the same number of jumps and cmoves,
        /// but jumps after all the cmoves have been executed, which
        /// would have very detrimental performance for shifts by 0.
        ///
        /// ## Branch on Zero (1st Algorithm)
        ///
        /// ```rust,ignore
        /// if shift >= BITS {
        ///     let hi = x1.wrapping_shl(BITS - 1);
        ///     let lo = x1.wrapping_shl(shift - BITS);
        ///     (lo as u128, hi)
        /// } else if shift == 0 {
        ///     (x0, x1)
        /// } else {
        ///     let hi = x1.wrapping_shl(shift);
        ///     let lo = x0.wrapping_shl(shift);
        ///     let carry = (x0 as u128).wrapping_shr(BITS - shift);
        ///     (lo, hi | carry)
        /// }
        /// ```
        ///
        /// ## Full Branch on Carry (2nd Algorithm)
        ///
        /// ```rust, ignore
        /// if shift >= BITS {
        ///     let hi = x1.wrapping_shl(BITS - 1);
        ///     let lo = x1.wrapping_shl(shift - BITS);
        ///     (lo as u128, hi)
        /// } else {
        ///     let hi = x1.wrapping_shl(shift);
        ///     let lo = x0.wrapping_shl(shift);
        ///     let is_zero = shift == 0;
        ///     match (x0 as u128).checked_shr(BITS - shift) {
        ///         Some(carry) => (lo, hi | carry),
        ///         None => (lo, hi),
        ///     }
        /// }
        /// ```
        ///
        /// ## Get Carry via Branch (3rd Algorithm)
        ///
        /// ```rust, ignore
        /// if shift >= BITS {
        ///     let hi = x1.wrapping_shl(BITS - 1);
        ///     let lo = x1.wrapping_shl(shift - BITS);
        ///     (lo as u128, hi)
        /// } else {
        ///     let hi = x1.wrapping_shl(shift);
        ///     let lo = x0.wrapping_shl(shift);
        ///     let is_zero = shift == 0;
        ///     let carry = match (x0 as u128).checked_shr(BITS - shift) {
        ///         Some(carry) => carry,
        ///         None => 0,
        ///     };
        ///     (lo, hi | carry)
        /// }
        /// ```
        #[inline]
        pub const fn $shl<const N: usize>(x: [$u; N], shift: u32) -> [$u; N] {
            assert!(N >= 2, "must have at least 2 limbs");
            debug_assert!(<$u>::BITS == <$s>::BITS);

            const BITS: u32 = <$u>::BITS;
            debug_assert!(shift < 2 * BITS, "attempt to shift left with overflow");
            let limb_n = shift as usize >> BITS.trailing_zeros();
            let bits_n = shift & (BITS - 1);
            let inv_n = BITS - bits_n;

            let mut result = [0; N];
            if N == 2 {
                // Simple case, only have to worry about swapping bits, no digits.
                let x0 = ne_index!(x[0]);
                let x1 = ne_index!(x[1]) as $s;
                let (r0, r1) = if limb_n != 0 {
                    let hi = x0 << bits_n;
                    (0, hi as $s)
                } else if shift == 0 {
                    (x0, x1)
                } else {
                    let hi = x1 << shift;
                    let lo = x0 << shift;
                    let carry = x0 >> inv_n;
                    (lo, hi | carry as $s)
                };
                ne_index!(result[0] = r0);
                ne_index!(result[1] = r1 as $u);
            } else if bits_n != 0 {
                let mut index = limb_n;
                let mut carry = 0;
                while index < N {
                    let xi = ne_index!(x[index - limb_n]);
                    ne_index!(result[index] = (xi << bits_n) | carry);
                    carry = xi >> inv_n;
                    index += 1;
                }
            } else {
                let mut index = limb_n;
                while index < N {
                    let xi = ne_index!(x[index - limb_n]);
                    ne_index!(result[index] = xi);
                    index += 1;
                }
            }

            result
        }

        /// Const implementation of `Shr` for internal algorithm use.
        ///
        /// Rust follows the C++20 semantics for this: `a >> b` is equal to
        /// `a / 2^b`, rounded-down to -Inf. So, `-a >> b` will be never go
        /// to `0`, at worst it will be `-1`.
        ///
        /// On x86, this is done via the `sar` instruction, which is quite
        /// efficient.
        ///
        /// # Design & Assembly
        ///
        /// There were 3 different variants attempted, of which the
        /// 1st had the best performance for `u128` but the 3rd had
        /// the best for `u64` and smaller. However, the performance
        /// for each was practically identical.
        ///
        /// All 3 have identical ASM for the 1st branch generated,
        /// just as expected, if the shift is larger than the number
        /// of bits. The 1st then speculatively jumps on zero, which
        /// branch prediction will likely almost always skip this
        /// jump (since shift-by-zero is unlikely to occur.) The
        /// 3rd replaces all but the first jump wit `cmove`, but
        /// since branch prediction is excellent here likely hurts
        /// overall performance. The 2nd case is the worst of both
        /// worlds: it keeps the same number of jumps and cmoves,
        /// but jumps after all the cmoves have been executed, which
        /// would have very detrimental performance for shifts by 0.
        ///
        /// ## Branch on Zero (1st Algorithm)
        ///
        /// ```rust,ignore
        /// if shift >= BITS {
        ///     let hi = x1.wrapping_shr(BITS - 1);
        ///     let lo = x1.wrapping_shr(shift - BITS);
        ///     (lo as u128, hi)
        /// } else if shift == 0 {
        ///     (x0, x1)
        /// } else {
        ///     let hi = x1.wrapping_shr(shift);
        ///     let lo = x0.wrapping_shr(shift);
        ///     let carry = (x0 as u128).wrapping_shl(BITS - shift);
        ///     (lo, hi | carry)
        /// }
        /// ```
        ///
        /// ## Full Branch on Carry (2nd Algorithm)
        ///
        /// ```rust, ignore
        /// if shift >= BITS {
        ///     let hi = x1.wrapping_shr(BITS - 1);
        ///     let lo = x1.wrapping_shr(shift - BITS);
        ///     (lo as u128, hi)
        /// } else {
        ///     let hi = x1.wrapping_shr(shift);
        ///     let lo = x0.wrapping_shr(shift);
        ///     let is_zero = shift == 0;
        ///     match (x0 as u128).checked_shl(BITS - shift) {
        ///         Some(carry) => (lo, hi | carry),
        ///         None => (lo, hi),
        ///     }
        /// }
        /// ```
        ///
        /// ## Get Carry via Branch (3rd Algorithm)
        ///
        /// ```rust, ignore
        /// if shift >= BITS {
        ///     let hi = x1.wrapping_shr(BITS - 1);
        ///     let lo = x1.wrapping_shr(shift - BITS);
        ///     (lo as u128, hi)
        /// } else {
        ///     let hi = x1.wrapping_shr(shift);
        ///     let lo = x0.wrapping_shr(shift);
        ///     let is_zero = shift == 0;
        ///     let carry = match (x0 as u128).checked_shl(BITS - shift) {
        ///         Some(carry) => carry,
        ///         None => 0,
        ///     };
        ///     (lo, hi | carry)
        /// }
        /// ```
        #[inline]
        pub const fn $shr<const N: usize>(x: [$u; N], shift: u32) -> [$u; N] {
            assert!(N >= 2, "must have at least 2 limbs");
            debug_assert!(<$u>::BITS == <$s>::BITS);

            const BITS: u32 = <$u>::BITS;
            debug_assert!(shift < 2 * BITS, "attempt to shift right with overflow");
            let limb_n = shift as usize >> BITS.trailing_zeros();
            let bits_n = shift & (BITS - 1);
            let inv_n = BITS - bits_n;

            let mut result = if (ne_index!(x[N - 1]) as $s) >= 0 {
                [0; N]
            } else {
                [<$u>::MAX; N]
            };

            if N == 2 {
                // Simple case, only have to worry about swapping bits, no digits.
                let x0 = ne_index!(x[0]);
                let x1 = ne_index!(x[1]) as $s;
                let (r0, r1) = if shift >= BITS {
                    // NOTE: The MSB is 0 if positive and 1 if negative, so this will
                    // always shift to 0 if positive and `-1` if negative.
                    let hi = x1 >> BITS - 1;
                    let lo = x1 >> shift - BITS;
                    (lo as $u, hi)
                } else if shift == 0 {
                    (x0, x1)
                } else {
                    let hi = x1 >> shift;
                    let lo = x0 >> shift;
                    let carry = (x1 as $u) << (BITS - shift);
                    (lo | carry, hi)
                };
                ne_index!(result[0] = r0);
                ne_index!(result[1] = r1 as $u);
            } else if bits_n != 0 {
                let mut index = N;
                let mut carry = 0;
                while index > limb_n {
                    index -= 1;
                    let xi = ne_index!(x[index]);
                    // need to round towards negative infinity
                    let ri = if index == N - 1 {
                        ((xi as $s) >> bits_n) as $u
                    } else {
                        xi >> bits_n
                    };
                    ne_index!(result[index - limb_n] = ri | carry);
                    carry = xi << inv_n;
                }
            } else {
                let mut index = N;
                while index > limb_n {
                    index -= 1;
                    let xi = ne_index!(x[index]);
                    ne_index!(result[index - limb_n] = xi);
                }
            }

            result
        }
    )*);
}

shift_signed_impl! {
    u32, i32 => shl_i32, shr_i32,
    u64, i64 => shl_i64, shr_i64,
    u128, i128 => shl_i128, shr_i128,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn from_le_wrap<T: Copy>(
        x: &[T; 2],
        y: &[T; 2],
        cb: impl Fn(&[T; 2], &[T; 2]) -> [T; 2],
    ) -> [T; 2] {
        if cfg!(target_endian = "big") {
            let result = cb(&[x[1], x[0]], &[y[1], y[0]]);
            [result[1], result[0]]
        } else {
            cb(x, y)
        }
    }

    fn from_le_over<T: Copy>(
        x: &[T; 2],
        y: &[T; 2],
        cb: impl Fn(&[T; 2], &[T; 2]) -> ([T; 2], bool),
    ) -> ([T; 2], bool) {
        if cfg!(target_endian = "big") {
            let (result, overflowed) = cb(&[x[1], x[0]], &[y[1], y[0]]);
            ([result[1], result[0]], overflowed)
        } else {
            cb(x, y)
        }
    }

    fn from_le_limb_wrap<T: Copy>(x: &[T; 2], y: T, cb: impl Fn(&[T; 2], T) -> [T; 2]) -> [T; 2] {
        if cfg!(target_endian = "big") {
            let result = cb(&[x[1], x[0]], y);
            [result[1], result[0]]
        } else {
            cb(x, y)
        }
    }

    fn from_le_limb_over<T: Copy>(
        x: &[T; 2],
        y: T,
        cb: impl Fn(&[T; 2], T) -> ([T; 2], bool),
    ) -> ([T; 2], bool) {
        if cfg!(target_endian = "big") {
            let (result, overflowed) = cb(&[x[1], x[0]], y);
            ([result[1], result[0]], overflowed)
        } else {
            cb(x, y)
        }
    }

    #[test]
    fn overflowing_add_u32_test() {
        assert_eq!(from_le_over(&[1, 0], &[1, 0], overflowing_add_u32), ([2, 0], false));
        assert_eq!(
            from_le_over(&[u32::MAX, 0], &[u32::MAX, 0], overflowing_add_u32),
            ([u32::MAX - 1, 1], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, 1], &[u32::MAX, 0], overflowing_add_u32),
            ([u32::MAX - 1, 2], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, u32::MAX], &[1, 0], overflowing_add_u32),
            ([0, 0], true)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, u32::MAX], &[2, 0], overflowing_add_u32),
            ([1, 0], true)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, u32::MAX], &[u32::MAX, u32::MAX], overflowing_add_u32),
            ([u32::MAX - 1, u32::MAX], true)
        );
    }

    #[test]
    fn overflowing_sub_u32_test() {
        assert_eq!(
            from_le_over(&[0, 0], &[1, 0], overflowing_sub_u32),
            ([u32::MAX, u32::MAX], true)
        );
        assert_eq!(from_le_over(&[1, 0], &[1, 0], overflowing_sub_u32), ([0, 0], false));
        assert_eq!(from_le_over(&[1, 0], &[0, 0], overflowing_sub_u32), ([1, 0], false));
        assert_eq!(
            from_le_over(&[u32::MAX, 1], &[0, 2], overflowing_sub_u32),
            ([u32::MAX, u32::MAX], true)
        );
        assert_eq!(from_le_over(&[0, 1], &[0, 2], overflowing_sub_u32), ([0, 4294967295], true));
        assert_eq!(
            from_le_over(&[0, 1], &[1, 1], overflowing_sub_u32),
            ([u32::MAX, u32::MAX], true)
        );
    }

    #[test]
    fn overflowing_mul_u32_test() {
        assert_eq!(
            from_le_over(&[u32::MAX, u32::MAX], &[u32::MAX, u32::MAX], overflowing_mul_u32),
            ([1, 0], true)
        );
        assert_eq!(
            from_le_over(&[1, 0], &[u32::MAX, 1], overflowing_mul_u32),
            ([u32::MAX, 1], false)
        );
        assert_eq!(from_le_over(&[2, 0], &[2147483648, 0], overflowing_mul_u32), ([0, 1], false));
        assert_eq!(from_le_over(&[1, 0], &[1, 0], overflowing_mul_u32), ([1, 0], false));
        assert_eq!(from_le_over(&[1, 0], &[0, 0], overflowing_mul_u32), ([0, 0], false));
        assert_eq!(
            from_le_over(&[u32::MAX, 1], &[0, 2], overflowing_mul_u32),
            ([0, u32::MAX - 1], true)
        );
        assert_eq!(from_le_over(&[0, 1], &[0, 2], overflowing_mul_u32), ([0, 0], true));
        // NOTE: This fails for small
        assert_eq!(from_le_over(&[67, 0], &[64103990, 0], overflowing_mul_u32), ([34, 1], false));
    }

    #[test]
    fn wrapping_mul_limb_u32_test() {
        assert_eq!(from_le_limb_wrap(&[67, 0], 64103990, wrapping_mul_limb_u32), [34, 1]);
        assert_eq!(from_le_limb_wrap(&[2, 0], 2147483648, wrapping_mul_limb_u32), [0, 1]);
        assert_eq!(from_le_limb_wrap(&[0, 2147483648], 2, wrapping_mul_limb_u32), [0, 0]);
        assert_eq!(from_le_limb_wrap(&[2, 2147483648], 2, wrapping_mul_limb_u32), [4, 0]);
        assert_eq!(from_le_limb_wrap(&[2147483647, 2147483647], 2, wrapping_mul_limb_u32), [
            4294967294, 4294967294
        ]);
    }

    #[test]
    fn overflowing_mul_limb_u32_test() {
        assert_eq!(
            from_le_limb_over(&[67, 0], 64103990, overflowing_mul_limb_u32),
            ([34, 1], false)
        );
        assert_eq!(
            from_le_limb_over(&[2, 0], 2147483648, overflowing_mul_limb_u32),
            ([0, 1], false)
        );
        assert_eq!(
            from_le_limb_over(&[0, 2147483648], 2, overflowing_mul_limb_u32),
            ([0, 0], true)
        );
        assert_eq!(
            from_le_limb_over(&[2, 2147483648], 2, overflowing_mul_limb_u32),
            ([4, 0], true)
        );
        assert_eq!(
            from_le_limb_over(&[2147483647, 2147483647], 2, overflowing_mul_limb_u32),
            ([4294967294, 4294967294], false)
        );
    }

    fn from_le_shift<T: Copy + Default, const N: usize>(
        x: [T; N],
        y: u32,
        cb: impl Fn([T; N], u32) -> [T; N],
    ) -> [T; N] {
        if cfg!(target_endian = "big") {
            let mut inv = [T::default(); N];
            let mut index = 0;
            while index < N {
                inv[index] = x[N - index - 1];
                index += 1;
            }

            let result = cb(inv, y);
            let mut index = 0;
            while index < N {
                inv[index] = result[N - index - 1];
                index += 1;
            }
            inv
        } else {
            cb(x, y)
        }
    }

    #[test]
    fn shl_u32_test() {
        assert_eq!(from_le_shift([1, 0], 1, shl_u32), [2, 0]);
        assert_eq!(from_le_shift([0, 1], 0, shl_u32), [0, 1]);
        assert_eq!(from_le_shift([0, 1], 1, shl_u32), [0, 2]);
        assert_eq!(from_le_shift([1, 0], 32, shl_u32), [0, 1]);
        assert_eq!(from_le_shift([0, 1], 32, shl_u32), [0, 0]);
        assert_eq!(from_le_shift([2, 0], 31, shl_u32), [0, 1]);
        assert_eq!(from_le_shift([0, 2], 31, shl_u32), [0, 0]);
        assert_eq!(from_le_shift([1, 2], 31, shl_u32), [2147483648, 0]);

        // try some digit shifts as well
        assert_eq!(from_le_shift([1, 2, 3], 31, shl_u32), [2147483648, 0, 2147483649]);
        assert_eq!(from_le_shift([1, 2, 0], 31, shl_u32), [2147483648, 0, 1]);
        assert_eq!(from_le_shift([1, 2, 3], 32, shl_u32), [0, 1, 2]);
        assert_eq!(from_le_shift([1, 2, 3], 63, shl_u32), [0, 2147483648, 0]);
        assert_eq!(from_le_shift([1, 2, 3], 64, shl_u32), [0, 0, 1]);
        assert_eq!(from_le_shift([1, 2, 3], 95, shl_u32), [0, 0, 2147483648]);
        assert_eq!(from_le_shift([1, 2, 3], 0, shl_u32), [1, 2, 3]);
    }

    #[test]
    fn shr_u32_test() {
        assert_eq!(from_le_shift([1, 0], 1, shr_u32), [0, 0]);
        assert_eq!(from_le_shift([0, 1], 0, shr_u32), [0, 1]);
        assert_eq!(from_le_shift([0, 1], 1, shr_u32), [2147483648, 0]);
        assert_eq!(from_le_shift([1, 0], 32, shr_u32), [0, 0]);
        assert_eq!(from_le_shift([0, 1], 32, shr_u32), [1, 0]);
        assert_eq!(from_le_shift([2, 0], 31, shr_u32), [0, 0]);
        assert_eq!(from_le_shift([0, 2], 31, shr_u32), [4, 0]);
        assert_eq!(from_le_shift([1, 2], 31, shr_u32), [4, 0]);

        // try some digit shifts as well
        assert_eq!(from_le_shift([1, 2, 3], 31, shr_u32), [4, 6, 0]);
        assert_eq!(from_le_shift([1, 2, 0], 31, shr_u32), [4, 0, 0]);
        assert_eq!(from_le_shift([1, 2, 3], 32, shr_u32), [2, 3, 0]);
        assert_eq!(from_le_shift([1, 2, 3], 63, shr_u32), [6, 0, 0]);
        assert_eq!(from_le_shift([1, 2, 3], 64, shr_u32), [3, 0, 0]);
        assert_eq!(from_le_shift([1, 2, 3], 95, shr_u32), [0, 0, 0]);
        assert_eq!(from_le_shift([1, 2, 3], 0, shr_u32), [1, 2, 3]);
    }

    #[test]
    fn overflowing_add_i32_test() {
        assert_eq!(from_le_over(&[1, 0], &[1, 0], overflowing_add_i32), ([2, 0], false));
        assert_eq!(
            from_le_over(&[u32::MAX, 0], &[u32::MAX, 0], overflowing_add_i32),
            ([u32::MAX - 1, 1], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, 1], &[u32::MAX, 0], overflowing_add_i32),
            ([u32::MAX - 1, 2], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, i32::MAX as u32], &[1, 0], overflowing_add_i32),
            ([0, i32::MIN as u32], true)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, i32::MAX as u32], &[2, 0], overflowing_add_i32),
            ([1, i32::MIN as u32], true)
        );
        assert_eq!(
            from_le_over(
                &[u32::MAX, i32::MAX as u32],
                &[u32::MAX, i32::MAX as u32],
                overflowing_add_i32
            ),
            ([u32::MAX - 1, -1i32 as u32], true)
        );
    }

    #[test]
    fn wrapping_mul_i32_test() {
        assert_eq!(from_le_wrap(&[1, 0], &[0, 1], wrapping_mul_i32), [0, 1]);
        assert_eq!(from_le_wrap(&[u32::MAX, u32::MAX], &[1, 0], wrapping_mul_i32), [
            u32::MAX,
            u32::MAX
        ]);
    }

    #[test]
    fn overflowing_mul_i32_test() {
        // -1 * -2^31, which should wrap exactly
        assert_eq!(
            from_le_over(&[u32::MAX, u32::MAX], &[0, i32::MIN as u32], overflowing_mul_i32),
            ([0, i32::MIN as u32], true)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, u32::MAX], &[0, i32::MAX as u32], overflowing_mul_i32),
            ([0, -i32::MAX as u32], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, u32::MAX], &[0, 0x80000000u32], overflowing_mul_i32),
            ([0, i32::MIN as u32], true)
        );
        assert_eq!(
            from_le_over(&[0, i32::MIN as u32], &[1, 0], overflowing_mul_i32),
            ([0, i32::MIN as u32], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, i32::MIN as u32], &[1, 0], overflowing_mul_i32),
            ([u32::MAX, i32::MIN as u32], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, i32::MIN as u32], &[0, 0], overflowing_mul_i32),
            ([0, 0], false)
        );
    }
}
