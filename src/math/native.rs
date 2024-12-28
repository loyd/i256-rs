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
        let index = $x.len() - 1;
        let msl = ne_index!($x[index]) as $s;
        msl < 0
    }};
}

/// Negate a given value, via a carrying add.
#[doc(hidden)]
#[macro_export]
macro_rules! negate {
    ($x:ident, $n:expr, $lo:ty, $hi:ty) => {{
        let mut index = 0;
        let mut result = [0; $n];
        let mut v: $lo;
        let mut c = true;
        while index < N - 1 {
            let xi = !ne_index!($x[index]);
            (v, c) = xi.overflowing_add(c as $lo);
            ne_index!(result[index] = v);
            index += 1;
        }

        let xn = !ne_index!($x[index]) as $hi;
        let v = xn.wrapping_add(c as $hi);
        ne_index!(result[index] = v as $lo);

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
                // NOTE: This is likely due to a miscompilation but this
                // is significantly faster than indexing within the loop
                // on `x86_64`.
                let xi = ne_index!(x[i]);
                while j < N {
                    // NOTE: This repeats but it keeps the previous result
                    // `r[ij]` as current.
                    let ij = i + j;
                    let yj = ne_index!(y[j]);
                    if ij < M {
                        // FIXME: Replace with `carrying_mul` when we add it
                        let full = (xi as $w) * (yj as $w);
                        let prod = carry as $w + ne_index!(r[ij]) as $w + full;
                        ne_index!(r[ij] = prod as $t);
                        carry = (prod >> SHIFT) as $t;
                    } else if xi != 0 && yj != 0 {
                        break;
                    }
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
                        let full = (xi as $w) * (yj as $w);
                        let prod = carry as $w + ne_index!(r[ij]) as $w + full;
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
        pub const fn $shl(x0: $u, x1: $u, shift: u32) -> ($u, $u) {
            const BITS: u32 = <$u>::BITS;
            debug_assert!(shift < 2 * BITS, "attempt to shift left with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                (0, x0.wrapping_shl(shift - BITS))
            } else if shift == 0 {
                (x0, x1)
            } else {
                // NOTE: We have `0xABCD_EFGH`, and we want to shift by 1,
                // so to `0xBCDE_FGH0`, or we need to carry the `D`. So,
                // our mask needs to be `0x000X`, or `0xXXXX >> (4 - 1)`,
                // and then the value needs to be shifted left `<< (4 - 1)`.
                let hi = x1.wrapping_shl(shift);
                let lo = x0.wrapping_shl(shift);
                let carry = x0.wrapping_shr(BITS - shift);
                (lo, hi | carry)
            }
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
        pub const fn $shr(x0: $u, x1: $u, shift: u32) -> ($u, $u) {
            const BITS: u32 = <$u>::BITS;
            debug_assert!(shift < 2 * BITS, "attempt to shift right with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                (x1.wrapping_shr(shift - BITS), 0)
            } else if shift == 0 {
                (x0, x1)
            } else {
                // NOTE: We have `0xABCD_EFGH`, and we want to shift by 1,
                // so to `0x0ABC_DEFG`, or we need to carry the `D`. So,
                // our mask needs to be `0x000X`, or `0xXXXX >> (4 - 1)`,
                // and then the value needs to be shifted left `<< (4 - 1)`.
                let hi = x1.wrapping_shr(shift);
                let lo = x0.wrapping_shr(shift);
                let carry = x1.wrapping_shl(BITS - shift);
                (lo | carry, hi)
            }
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
        #[inline]
        pub const fn $left(x0:$u, x1: $u, n: u32) -> ($u, $u) {
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
            let n = n % (2 * BITS);
            let upper = n & !(BITS - 1);
            let n = n & (BITS - 1);
            let (x0, x1) = if upper != 0 {
                (x1, x0)
            } else {
                (x0, x1)
            };
            if n == 0 {
                (x0, x1)
            } else {
                let hi = (x1.wrapping_shl(n)) | (x0.wrapping_shr(BITS - n));
                let lo = (x0.wrapping_shl(n)) | (x1.wrapping_shr(BITS - n));
                (lo, hi)
            }
        }

        /// Shifts the bits to the right by a specified amount, `n`,
        /// wrapping the truncated bits to the beginning of the resulting
        /// integer.
        ///
        /// Please note this isn't the same operation as the `>>` shifting operator!
        #[inline]
        pub const fn $right(x0:$u, x1: $u, n: u32) -> ($u, $u) {
            // See rotate_left for the description
            // 0bFFFFXY -> 0bXYFFFF
            const BITS: u32 = <$u>::BITS;
            let n = n % (2 * BITS);
            let upper = n & !(BITS - 1);
            let n = n & (BITS - 1);
            let (x0, x1) = if upper != 0 {
                (x1, x0)
            } else {
                (x0, x1)
            };
            if n == 0 {
                (x0, x1)
            } else {
                let hi = (x1.wrapping_shr(n)) | (x0.wrapping_shl(BITS - n));
                let lo = (x0.wrapping_shr(n)) | (x1.wrapping_shl(BITS - n));
                (lo, hi)
            }
        }
    )*);
}

rotate_unsigned_impl! {
    u32 => rotate_left_u32, rotate_right_u32,
    u64 => rotate_left_u64, rotate_right_u64,
    u128 => rotate_left_u128, rotate_right_u128,
}

// Widening and narrowing conversions for primitive types.
macro_rules! unsigned_primitive_cast {
    (
        $u:ty,
        $s:ty,as_uwide =>
        $as_uwide:ident,as_unarrow =>
        $as_unarrow:ident,as_iwide =>
        $as_iwide:ident,as_inarrow =>
        $as_inarrow:ident,wide_cast =>
        $wide_cast:ident
    ) => {
        /// Convert an unsigned, narrow type to the wide type.
        #[inline(always)]
        pub const fn $as_uwide(x: $u) -> ($u, $u) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            (x, 0)
        }

        /// Convert a signed, narrow type to the wide type.
        ///
        /// This is the same logic, and codegen as `is_wide`
        /// for signed types, just we keep it as an unsigned type
        /// for `hi`.
        #[inline(always)]
        pub const fn $as_iwide(x: $s) -> ($u, $u) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let hi = <$u>::MIN.wrapping_sub(x.is_negative() as $u);
            (x as $u, hi)
        }

        /// Convert the wide value to a narrow, unsigned type.
        ///
        /// This is effectively a no-op.
        #[inline(always)]
        pub const fn $as_unarrow(x0: $u, x1: $u) -> $u {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let _ = x1;
            x0
        }

        /// Convert the wide value to a narrow, signed type.
        ///
        /// This is effectively a no-op.
        #[inline(always)]
        pub const fn $as_inarrow(x0: $u, x1: $u) -> $s {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let _ = x1;
            x0 as $s
        }

        /// Do a wide cast from unsigned to signed.
        ///
        /// This is effectively a no-op.
        #[inline(always)]
        pub const fn $wide_cast(x0: $u, x1: $u) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            (x0, x1 as $s)
        }
    };
}

unsigned_primitive_cast!(
    u32,
    i32,
    as_uwide => as_uwide_u32,
    as_unarrow => as_unarrow_u32,
    as_iwide => as_iwide_u32,
    as_inarrow => as_inarrow_u32,
    wide_cast => wide_cast_u32
);
unsigned_primitive_cast!(
    u64,
    i64,
    as_uwide => as_uwide_u64,
    as_unarrow => as_unarrow_u64,
    as_iwide => as_iwide_u64,
    as_inarrow => as_inarrow_u64,
    wide_cast => wide_cast_u64
);
unsigned_primitive_cast!(
    u128,
    i128,
    as_uwide => as_uwide_u128,
    as_unarrow => as_unarrow_u128,
    as_iwide => as_iwide_u128,
    as_inarrow => as_inarrow_u128,
    wide_cast => wide_cast_u128
);

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
            // general approach is unsigned multiplication, then convert
            // back to the signed variants by checking if both should be negative
            let mut x = *x;
            let mut y = *y;
            let x_is_negative = is_negative!(x, $s);
            let y_is_negative = is_negative!(y, $s);
            let should_be_negative = x_is_negative ^ y_is_negative;
            if x_is_negative {
                x = negate!(x, M, $u, $s);
            }
            if y_is_negative {
                y = negate!(y, N, $u, $s);
            }

            let mut r = $wrapping_unsigned(&x, &y);
            if should_be_negative {
                r = negate!(r, M, $u, $s);
            }

            r
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
            let mut rhs = [0; N];
            ne_index!(rhs[0] = y);
            $wrapping_full(&x, &rhs)
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
            let sign_bit = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let mut rhs = [sign_bit; N];
            ne_index!(rhs[0] = y as $u);
            $wrapping_full(&x, &rhs)
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
            let mut x = *x;
            let mut y = *y;
            let x_is_negative = is_negative!(x, $s);
            let y_is_negative = is_negative!(y, $s);
            let should_be_negative = x_is_negative ^ y_is_negative;
            if x_is_negative {
                x = negate!(x, M, $u, $s);
            }
            if y_is_negative {
                y = negate!(y, N, $u, $s);
            }

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
                r = negate!(r, M, $u, $s);
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
        pub const fn $shl(x0: $u, x1: $s, shift: u32) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            const BITS: u32 = <$u>::BITS;
            debug_assert!(shift < 2 * BITS, "attempt to shift right with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                let hi = x0.wrapping_shl(shift - BITS);
                (0, hi as $s)
            } else if shift == 0 {
                (x0, x1)
            } else {
                let hi = x1.wrapping_shl(shift);
                let lo = x0.wrapping_shl(shift);
                let carry = x0.wrapping_shr(BITS - shift);
                (lo, hi | carry as $s)
            }
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
        pub const fn $shr(x0: $u, x1: $s, shift: u32) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            const BITS: u32 = <$u>::BITS;
            debug_assert!(shift < 2 * BITS, "attempt to shift right with overflow");
            let shift = shift % (2 * BITS);
            if shift >= BITS {
                // NOTE: The MSB is 0 if positive and 1 if negative, so this will
                // always shift to 0 if positive and `-1` if negative.
                let hi = x1.wrapping_shr(BITS - 1);
                let lo = x1.wrapping_shr(shift - BITS);
                (lo as $u, hi)
            } else if shift == 0 {
                (x0, x1)
            } else {
                let hi = x1.wrapping_shr(shift);
                let lo = x0.wrapping_shr(shift);
                let carry = (x1 as $u).wrapping_shl(BITS - shift);
                (lo | carry, hi)
            }
        }
    )*);
}

shift_signed_impl! {
    u32, i32 => shl_i32, shr_i32,
    u64, i64 => shl_i64, shr_i64,
    u128, i128 => shl_i128, shr_i128,
}

// UNARY OPS - SIGNED
// ------------------

macro_rules! rotate_signed_impl {
    ($($u:ty, $s:ty => $left:ident, $right:ident,)*) => ($(
        /// Shifts the bits to the left by a specified amount, `n`,
        /// wrapping the truncated bits to the end of the resulting integer.
        ///
        /// This is identical to the unsigned variant: `T::MIN rol 1` is
        /// `1 as T`.
        ///
        /// # Assembly
        ///
        /// This is basically identical to the unsigned variant. It first
        /// conditionally swaps the low and high digits, jumps on zero,
        /// then performs 4 shifts and 2 ors to get the final results.
        ///
        /// ```asm
        /// rotate_left:
        ///     mov     r8d, edx
        ///     mov     eax, esi
        ///     test    r8b, 32
        ///     mov     edx, edi
        ///     cmove   edx, esi
        ///     cmove   eax, edi
        ///     mov     esi, r8d
        ///     and     esi, 31
        ///     je      .LBB
        ///     mov     edi, edx
        ///     mov     ecx, esi
        ///     shl     edi, cl
        ///     neg     r8b
        ///     mov     r9d, eax
        ///     mov     ecx, r8d
        ///     shr     r9d, cl
        ///     mov     ecx, esi
        ///     shl     eax, cl
        ///     mov     ecx, r8d
        ///     shr     edx, cl
        ///     or      r9d, edi
        ///     or      eax, edx
        ///     mov     edx, r9d
        /// .LBB:
        ///     ret
        /// ```
        #[inline]
        pub const fn $left(x0:$u, x1: $s, n: u32) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            // 0bXYFFFF -> 0bFFFFXY
            const BITS: u32 = <$u>::BITS;
            let n = n % (2 * BITS);
            let upper = n & !(BITS - 1);
            let n = n & (BITS - 1);
            let (x0, x1) = if upper != 0 {
                (x1 as $u, x0)
            } else {
                (x0, x1 as $u)
            };
            if n == 0 {
                (x0, x1 as $s)
            } else {
                let hi = (x1.wrapping_shl(n)) | (x0.wrapping_shr(BITS - n));
                let lo = (x0.wrapping_shl(n)) | (x1.wrapping_shr(BITS - n));
                (lo, hi as $s)
            }
        }

        /// Shifts the bits to the right by a specified amount, `n`,
        /// wrapping the truncated bits to the beginning of the resulting
        /// integer.
        ///
        /// Please note this isn't the same operation as the `>>` shifting operator!
        #[inline]
        pub const fn $right(x0:$u, x1: $s, n: u32) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            // 0bFFFFXY -> 0bXYFFFF
            const BITS: u32 = <$u>::BITS;
            let n = n % (2 * BITS);
            let upper = n & !(BITS - 1);
            let n = n & (BITS - 1);
            let (x0, x1) = if upper != 0 {
                (x1 as $u, x0)
            } else {
                (x0, x1 as $u)
            };
            if n == 0 {
                (x0, x1 as $s)
            } else {
                let hi = (x1.wrapping_shr(n)) | (x0.wrapping_shl(BITS - n));
                let lo = (x0.wrapping_shr(n)) | (x1.wrapping_shl(BITS - n));
                (lo, hi as $s)
            }
        }
    )*);
}

rotate_signed_impl! {
    u32, i32 => rotate_left_i32, rotate_right_i32,
    u64, i64 => rotate_left_i64, rotate_right_i64,
    u128, i128 => rotate_left_i128, rotate_right_i128,
}

// Widening and narrowing conversions for primitive types.
macro_rules! signed_primitive_cast {
    (
        $u:ty,
        $s:ty,as_uwide =>
        $as_uwide:ident,as_unarrow =>
        $as_unarrow:ident,as_iwide =>
        $as_iwide:ident,as_inarrow =>
        $as_inarrow:ident,wide_cast =>
        $wide_cast:ident
    ) => {
        // NOTE: This code was all test with the same algorithms in C++,
        // compiling for both little and big endian to ensure the logic
        // is the same, just as a precaution. For example:
        //
        // ```cpp
        // #include <cstdint>
        // #include <limits>
        //
        // int32_t as_inarrow_hard(int64_t v) {
        //     return (int32_t)v;
        // }
        //
        // int32_t as_inarrow_soft(int64_t v) {
        //     uint64_t mask = (uint64_t)std::numeric_limits<uint32_t>::max();
        //     uint64_t lo = ((uint64_t)v) & mask;
        //     return (int32_t)lo;
        // }
        // ```

        /// Convert an unsigned, narrow type to the wide type.
        ///
        /// This is the same as:
        ///
        /// ```rust
        /// #[inline(never)]
        /// pub const fn as_uwide(v: u32) -> u64 {
        ///     // hi bits will always be 0
        ///     v as u64
        /// }
        /// ```
        #[inline(always)]
        pub const fn $as_uwide(x: $u) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            (x, 0)
        }

        /// Convert a signed, narrow type to the wide type.
        ///
        /// This is the same as:
        ///
        /// ```rust
        /// #[inline(never)]
        /// pub const fn as_iwide_hard(v: i32) -> i64 {
        ///     v as i64
        /// }
        ///
        /// #[inline(never)]
        /// pub const fn as_iwide_soft(x: i32) -> i64 {
        ///     let hi = u32::MIN.wrapping_sub(x.is_negative() as u32) as u64;
        ///     let hi = hi << 32;
        ///     let lo = (x as u32) as u64;
        ///     let x = lo | hi;
        ///     return x as i64;
        /// }
        /// ```
        ///
        /// This is analogous to the following C++ code:
        ///
        /// ```cpp
        /// int64_t as_iwide_hard(int32_t v) {
        ///     return v;
        /// }
        ///
        /// int64_t as_iwide_soft(int32_t v) {
        ///     bool is_negative = v < 0;
        ///     uint64_t hi = uint64_t(0) - uint64_t(is_negative);
        ///     hi <<= 32;
        ///     uint64_t lo = (uint64_t)((uint32_t)v);
        ///     uint64_t x = lo | hi;
        ///     return (int64_t)x;
        /// }
        /// ```
        ///
        /// This is way more efficient than using naive approaches, like checking `< 0`
        /// which brings in a `test` instruction.
        ///
        /// # Assembly
        ///
        /// This gets optimizes out very nicely, as a bit shift for all integers.
        /// ```asm
        /// as_iwide_i64:
        ///     mov     rax, rdi
        ///     mov     rdx, rdi
        ///     sar     rdx, 63
        ///     ret
        ///
        /// as_iwide_i128:
        ///     mov     rax, rdi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     sar     rdx, 63
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 24], rdx
        ///     mov     qword ptr [rdi + 16], rdx
        ///     ret
        /// ```
        #[inline(always)]
        pub const fn $as_iwide(x: $s) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let hi = <$u>::MIN.wrapping_sub(x.is_negative() as $u);
            (x as $u, hi as $s)
        }

        /// Convert the wide value to a narrow, unsigned type.
        ///
        /// This is the same as:
        ///
        /// ```rust
        /// #[inline(never)]
        /// pub const fn as_unarrow_hard(v: i64) -> u32 {
        ///     v as u32
        /// }
        ///
        /// #[inline(never)]
        /// pub const fn as_unarrow_soft(v: i64) -> u32 {
        ///     const MASK: u64 = u32::MAX as u64;
        ///     let lo = (v as u64) & MASK;
        ///     lo as u32
        /// }
        /// ```
        #[inline(always)]
        pub const fn $as_unarrow(x0: $u, x1: $s) -> $u {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            _ = x1;
            x0 as $u
        }

        /// Convert the wide value to a narrow, signed type.
        ///
        /// This is the same as:
        ///
        /// ```rust
        /// #[inline(never)]
        /// pub const fn as_inarrow_hard(v: i64) -> i32 {
        ///     v as i32
        /// }
        ///
        /// #[inline(never)]
        /// pub const fn as_inarrow_soft(v: i64) -> i32 {
        ///     const MASK: u64 = u32::MAX as u64;
        ///     let lo = (v as u64) & MASK;
        ///     (lo as u32) as i32
        /// }
        /// ```
        #[inline(always)]
        pub const fn $as_inarrow(x0: $u, x1: $s) -> $s {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            _ = x1;
            x0 as $s
        }

        /// Do a wide cast from signed to unsigned.
        #[inline(always)]
        pub const fn $wide_cast(x0: $u, x1: $s) -> ($u, $u) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            (x0, x1 as $u)
        }
    };
}

signed_primitive_cast!(
    u32,
    i32,
    as_uwide => as_uwide_i32,
    as_unarrow => as_unarrow_i32,
    as_iwide => as_iwide_i32,
    as_inarrow => as_inarrow_i32,
    wide_cast => wide_cast_i32
);
signed_primitive_cast!(
    u64,
    i64,
    as_uwide => as_uwide_i64,
    as_unarrow => as_unarrow_i64,
    as_iwide => as_iwide_i64,
    as_inarrow => as_inarrow_i64,
    wide_cast => wide_cast_i64
);
signed_primitive_cast!(
    u128,
    i128,
    as_uwide => as_uwide_i128,
    as_unarrow => as_unarrow_i128,
    as_iwide => as_iwide_i128,
    as_inarrow => as_inarrow_i128,
    wide_cast => wide_cast_i128
);

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn overflowing_add_u32_test() {
        assert_eq!(overflowing_add_u32(&[1, 0], &[1, 0]), ([2, 0], false));
        assert_eq!(overflowing_add_u32(&[u32::MAX, 0], &[u32::MAX, 0]), ([u32::MAX - 1, 1], false));
        assert_eq!(overflowing_add_u32(&[u32::MAX, 1], &[u32::MAX, 0]), ([u32::MAX - 1, 2], false));
        assert_eq!(overflowing_add_u32(&[u32::MAX, u32::MAX], &[1, 0]), ([0, 0], true));
        assert_eq!(overflowing_add_u32(&[u32::MAX, u32::MAX], &[2, 0]), ([1, 0], true));
        assert_eq!(
            overflowing_add_u32(&[u32::MAX, u32::MAX], &[u32::MAX, u32::MAX]),
            ([u32::MAX - 1, u32::MAX], true)
        );
    }

    #[test]
    fn overflowing_sub_u32_test() {
        assert_eq!(overflowing_sub_u32(&[0, 0], &[1, 0]), ([u32::MAX, u32::MAX], true));
        assert_eq!(overflowing_sub_u32(&[1, 0], &[1, 0]), ([0, 0], false));
        assert_eq!(overflowing_sub_u32(&[1, 0], &[0, 0]), ([1, 0], false));
        assert_eq!(overflowing_sub_u32(&[u32::MAX, 1], &[0, 2]), ([u32::MAX, u32::MAX], true));
        assert_eq!(overflowing_sub_u32(&[0, 1], &[0, 2]), ([0, 4294967295], true));
        assert_eq!(overflowing_sub_u32(&[0, 1], &[1, 1]), ([u32::MAX, u32::MAX], true));
    }

    #[test]
    fn overflowing_mul_u32_test() {
        assert_eq!(
            overflowing_mul_u32(&[u32::MAX, u32::MAX], &[u32::MAX, u32::MAX]),
            ([1, 0], true)
        );
        assert_eq!(overflowing_mul_u32(&[1, 0], &[u32::MAX, 1]), ([u32::MAX, 1], false));
        assert_eq!(overflowing_mul_u32(&[2, 0], &[2147483648, 0]), ([0, 1], false));
        assert_eq!(overflowing_mul_u32(&[1, 0], &[1, 0]), ([1, 0], false));
        assert_eq!(overflowing_mul_u32(&[1, 0], &[0, 0]), ([0, 0], false));
        assert_eq!(overflowing_mul_u32(&[u32::MAX, 1], &[0, 2]), ([0, u32::MAX - 1], true));
        assert_eq!(overflowing_mul_u32(&[0, 1], &[0, 2]), ([0, 0], true));
        // NOTE: This fails for small
        assert_eq!(overflowing_mul_u32(&[67, 0], &[64103990, 0]), ([34, 1], false));
    }

    #[test]
    fn wrapping_mul_limb_u32_test() {
        assert_eq!(wrapping_mul_limb_u32(&[67, 0], 64103990), [34, 1]);
        assert_eq!(wrapping_mul_limb_u32(&[2, 0], 2147483648), [0, 1]);
        assert_eq!(wrapping_mul_limb_u32(&[0, 2147483648], 2), [0, 0]);
        assert_eq!(wrapping_mul_limb_u32(&[2, 2147483648], 2), [4, 0]);
        assert_eq!(wrapping_mul_limb_u32(&[2147483647, 2147483647], 2), [4294967294, 4294967294]);
    }

    #[test]
    fn overflowing_mul_limb_u32_test() {
        assert_eq!(overflowing_mul_limb_u32(&[67, 0], 64103990), ([34, 1], false));
        assert_eq!(overflowing_mul_limb_u32(&[2, 0], 2147483648), ([0, 1], false));
        assert_eq!(overflowing_mul_limb_u32(&[0, 2147483648], 2), ([0, 0], true));
        assert_eq!(overflowing_mul_limb_u32(&[2, 2147483648], 2), ([4, 0], true));
        assert_eq!(
            overflowing_mul_limb_u32(&[2147483647, 2147483647], 2),
            ([4294967294, 4294967294], false)
        );
    }

    #[test]
    fn shl_u32_test() {
        assert_eq!(shl_u32(1, 0, 1), (2, 0));
        assert_eq!(shl_u32(0, 1, 0), (0, 1));
        assert_eq!(shl_u32(0, 1, 1), (0, 2));
        assert_eq!(shl_u32(1, 0, 32), (0, 1));
        assert_eq!(shl_u32(0, 1, 32), (0, 0));
        assert_eq!(shl_u32(2, 0, 31), (0, 1));
        assert_eq!(shl_u32(0, 2, 31), (0, 0));
        assert_eq!(shl_u32(1, 2, 31), (2147483648, 0));
    }

    #[test]
    fn shr_u32_test() {
        assert_eq!(shr_u32(1, 0, 1), (0, 0));
        assert_eq!(shr_u32(0, 1, 0), (0, 1));
        assert_eq!(shr_u32(0, 1, 1), (2147483648, 0));
        assert_eq!(shr_u32(1, 0, 32), (0, 0));
        assert_eq!(shr_u32(0, 1, 32), (1, 0));
        assert_eq!(shr_u32(2, 0, 31), (0, 0));
        assert_eq!(shr_u32(0, 2, 31), (4, 0));
        assert_eq!(shr_u32(1, 2, 31), (4, 0));
    }

    #[test]
    fn overflowing_add_i32_test() {
        assert_eq!(overflowing_add_i32(&[1, 0], &[1, 0]), ([2, 0], false));
        assert_eq!(overflowing_add_i32(&[u32::MAX, 0], &[u32::MAX, 0]), ([u32::MAX - 1, 1], false));
        assert_eq!(overflowing_add_i32(&[u32::MAX, 1], &[u32::MAX, 0]), ([u32::MAX - 1, 2], false));
        assert_eq!(
            overflowing_add_i32(&[u32::MAX, i32::MAX as u32], &[1, 0]),
            ([0, i32::MIN as u32], true)
        );
        assert_eq!(
            overflowing_add_i32(&[u32::MAX, i32::MAX as u32], &[2, 0]),
            ([1, i32::MIN as u32], true)
        );
        assert_eq!(
            overflowing_add_i32(&[u32::MAX, i32::MAX as u32], &[u32::MAX, i32::MAX as u32]),
            ([u32::MAX - 1, -1i32 as u32], true)
        );
    }

    #[test]
    fn wrapping_mul_i32_test() {
        assert_eq!(wrapping_mul_i32(&[1, 0], &[0, 1]), [0, 1]);
        assert_eq!(wrapping_mul_i32(&[u32::MAX, u32::MAX], &[1, 0]), [u32::MAX, u32::MAX]);
    }

    #[test]
    fn overflowing_mul_i32_test() {
        // -1 * -2^31, which should wrap exactly
        assert_eq!(
            overflowing_mul_i32(&[u32::MAX, u32::MAX], &[0, i32::MIN as u32]),
            ([0, i32::MIN as u32], true)
        );
        assert_eq!(
            overflowing_mul_i32(&[u32::MAX, u32::MAX], &[0, i32::MAX as u32]),
            ([0, -i32::MAX as u32], false)
        );
        assert_eq!(
            overflowing_mul_i32(&[u32::MAX, u32::MAX], &[0, 0x80000000u32]),
            ([0, i32::MIN as u32], true)
        );
        assert_eq!(
            overflowing_mul_i32(&[0, i32::MIN as u32], &[1, 0]),
            ([0, i32::MIN as u32], false)
        );
        assert_eq!(
            overflowing_mul_i32(&[u32::MAX, i32::MIN as u32], &[1, 0]),
            ([u32::MAX, i32::MIN as u32], false)
        );
        assert_eq!(overflowing_mul_i32(&[u32::MAX, i32::MIN as u32], &[0, 0]), ([0, 0], false));
    }
}
