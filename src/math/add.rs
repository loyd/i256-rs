//! Const implementations of addition.

use super::bigint::*;
use crate::{ILimb, IWide, ULimb, UWide};

macro_rules! unsigned_define {
    (
        type =>
        $u:ty,wide =>
        $w:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_limb =>
        $wrapping_limb:ident,overflowing_limb =>
        $overflowing_limb:ident,wrapping_wide =>
        $wrapping_wide:ident,overflowing_wide =>
        $overflowing_wide:ident,wrapping_mn =>
        $wrapping_mn:ident,overflowing_mn =>
        $overflowing_mn:ident,carrying =>
        $carrying:ident $(,)?
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
            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            let mut vi: $u;
            while index < N - 1 {
                (vi, c) = $carrying(ne_index!(x[index]), ne_index!(y[index]), c);
                ne_index!(result[index] = vi);
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
            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            let mut vi: $u;
            while index < N {
                (vi, c) = $carrying(ne_index!(x[index]), ne_index!(y[index]), c);
                ne_index!(result[index] = vi);
                index += 1;
            }

            (result, c)
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
            while index < N {
                (v, c) = ne_index!(x[index]).overflowing_add(c as $u);
                ne_index!(result[index] = v);
                index += 1;
            }

            (result, c)
        }

        /// Const implementation of `wrapping_add` for internal algorithm use.
        // NOTE: This differs significantly from `wrapping_full`.
        #[inline]
        pub const fn $wrapping_mn<const M: usize, const N: usize>(
            x: &[$u; M],
            y: &[$u; N],
        ) -> [$u; M] {
            assert!(N >= 2 && M > N);

            let mut index = 0;
            let mut result = [0; M];
            let mut c: bool = false;
            let mut vi: $u;

            while index < N {
                (vi, c) = $carrying(ne_index!(x[index]), ne_index!(y[index]), c);
                ne_index!(result[index] = vi);
                index += 1;
            }

            while index < M - 1 {
                (vi, c) = ne_index!(x[index]).overflowing_add(c as $u);
                ne_index!(result[index] = vi);
                index += 1;
            }
            ne_index!(result[index] = ne_index!(x[index]).wrapping_add(c as $u));

            result
        }

        /// Const implementation of `overflowing_add` for internal algorithm use.
        // NOTE: This differs significantly from `overflowing_full`.
        #[inline]
        pub const fn $overflowing_mn<const M: usize, const N: usize>(
            x: &[$u; M],
            y: &[$u; N],
        ) -> ([$u; M], bool) {
            assert!(N >= 2 && M > N);

            let mut index = 0;
            let mut result = [0; M];
            let mut c: bool = false;
            let mut vi: $u;

            while index < N {
                (vi, c) = $carrying(ne_index!(x[index]), ne_index!(y[index]), c);
                ne_index!(result[index] = vi);
                index += 1;
            }

            while index < M {
                (vi, c) = ne_index!(x[index]).overflowing_add(c as $u);
                ne_index!(result[index] = vi);
                index += 1;
            }

            (result, c)
        }

        /// Const implementation of `wrapping_add` a small number to the wider type.
        #[inline]
        pub const fn $wrapping_wide<const N: usize>(x: &[$u; N], y: $w) -> [$u; N] {
            let mut rhs = [0; 2];
            ne_index!(rhs[0] = y as $u);
            ne_index!(rhs[1] = (y >> <$u>::BITS) as $u);
            $wrapping_mn(x, &rhs)
        }

        /// Const implementation of `overflowing_add` a small number to the wider type.
        #[inline]
        pub const fn $overflowing_wide<const N: usize>(x: &[$u; N], y: $w) -> ([$u; N], bool) {
            let mut rhs = [0; 2];
            ne_index!(rhs[0] = y as $u);
            ne_index!(rhs[1] = (y >> <$u>::BITS) as $u);
            $overflowing_mn(x, &rhs)
        }
    };
}

unsigned_define!(
    type => u32,
    wide => u64,
    wrapping_full => wrapping_u32,
    overflowing_full => overflowing_u32,
    wrapping_limb => wrapping_limb_u32,
    overflowing_limb => overflowing_limb_u32,
    wrapping_wide => wrapping_wide_u32,
    overflowing_wide => overflowing_wide_u32,
    wrapping_mn => wrapping_mn_u32,
    overflowing_mn => overflowing_mn_u32,
    carrying => carrying_add_u32,
);
unsigned_define!(
    type => u64,
    wide => u128,
    wrapping_full => wrapping_u64,
    overflowing_full => overflowing_u64,
    wrapping_limb => wrapping_limb_u64,
    overflowing_limb => overflowing_limb_u64,
    wrapping_wide => wrapping_wide_u64,
    overflowing_wide => overflowing_wide_u64,
    wrapping_mn => wrapping_mn_u64,
    overflowing_mn => overflowing_mn_u64,
    carrying => carrying_add_u64,
);

limb_function!(wrapping_unsigned, wrapping_u64, wrapping_u32, &[ULimb; N], ret => [ULimb; N]);
limb_function!(overflowing_unsigned, overflowing_u64, overflowing_u32, &[ULimb; N], &[ULimb; N], ret => ([ULimb; N], bool));

// limb
limb_function!(wrapping_limb, wrapping_limb_u64, wrapping_limb_u32, &[ULimb; N], ULimb, ret => [ULimb; N]);
limb_function!(overflowing_limb, overflowing_limb_u64, overflowing_limb_u32, &[ULimb; N], ULimb, ret => ([ULimb; N], bool));

// wide
limb_function!(wrapping_wide, wrapping_wide_u64, wrapping_wide_u32, &[ULimb; N], UWide, ret => [ULimb; N]);
limb_function!(overflowing_wide, overflowing_wide_u64, overflowing_wide_u32, &[ULimb; N], UWide, ret => ([ULimb; N], bool));

macro_rules! signed_define {
    (
        unsigned =>
        $u:ty,signed =>
        $s:ty,unsigned_wide =>
        $uw:ty,signed_wide =>
        $sw:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_ulimb =>
        $wrapping_ulimb:ident,overflowing_ulimb =>
        $overflowing_ulimb:ident,wrapping_ilimb =>
        $wrapping_ilimb:ident,overflowing_ilimb =>
        $overflowing_ilimb:ident,wrapping_uwide =>
        $wrapping_uwide:ident,overflowing_uwide =>
        $overflowing_uwide:ident,wrapping_iwide =>
        $wrapping_iwide:ident,overflowing_iwide =>
        $overflowing_iwide:ident,carrying =>
        $carrying:ident $(,)?
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
            assert!(<$u>::BITS == <$s>::BITS);
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            let mut vi: $u;
            while index < N - 1 {
                (vi, c) = $carrying(ne_index!(x[index]), ne_index!(y[index]), c);
                ne_index!(result[index] = vi);
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
            assert!(<$u>::BITS == <$s>::BITS);
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            let mut vi: $u;
            while index < N - 1 {
                (vi, c) = $carrying(ne_index!(x[index]), ne_index!(y[index]), c);
                ne_index!(result[index] = vi);
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

        /// Const implementation to add a small, unsigned number to the wider type.
        pub const fn $wrapping_uwide<const N: usize>(x: &[$u; N], y: $uw) -> [$u; N] {
            let mut rhs = [0; N];
            ne_index!(rhs[0] = y as $u);
            ne_index!(rhs[1] = (y >> <$u>::BITS) as $u);
            $wrapping_full(x, &rhs)
        }

        /// Const implementation to add a small, unsigned number to the wider type.
        pub const fn $overflowing_uwide<const N: usize>(x: &[$u; N], y: $uw) -> ([$u; N], bool) {
            let mut rhs = [0; N];
            ne_index!(rhs[0] = y as $u);
            ne_index!(rhs[1] = (y >> <$u>::BITS) as $u);
            $overflowing_full(x, &rhs)
        }

        /// Const implementation to add a small, signed number to the wider type.
        pub const fn $wrapping_iwide<const N: usize>(x: &[$u; N], y: $sw) -> [$u; N] {
            let sign_bit = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let mut rhs = [sign_bit; N];
            let y = y as $uw;
            ne_index!(rhs[0] = y as $u);
            ne_index!(rhs[1] = (y >> <$u>::BITS) as $u);
            $wrapping_full(x, &rhs)
        }

        /// Const implementation to add a small, signed number to the wider type.
        pub const fn $overflowing_iwide<const N: usize>(x: &[$u; N], y: $sw) -> ([$u; N], bool) {
            let sign_bit = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let mut rhs = [sign_bit; N];
            let y = y as $uw;
            ne_index!(rhs[0] = y as $u);
            ne_index!(rhs[1] = (y >> <$u>::BITS) as $u);
            $overflowing_full(x, &rhs)
        }
    };
}

signed_define!(
    unsigned => u32,
    signed => i32,
    unsigned_wide => u64,
    signed_wide => i64,
    wrapping_full => wrapping_i32,
    overflowing_full => overflowing_i32,
    wrapping_ulimb => wrapping_ulimb_i32,
    overflowing_ulimb => overflowing_ulimb_i32,
    wrapping_ilimb => wrapping_ilimb_i32,
    overflowing_ilimb => overflowing_ilimb_i32,
    wrapping_uwide => wrapping_uwide_i32,
    overflowing_uwide => overflowing_uwide_i32,
    wrapping_iwide => wrapping_iwide_i32,
    overflowing_iwide => overflowing_iwide_i32,
    carrying => carrying_add_u32,
);
signed_define!(
    unsigned => u64,
    signed => i64,
    unsigned_wide => u128,
    signed_wide => i128,
    wrapping_full => wrapping_i64,
    overflowing_full => overflowing_i64,
    wrapping_ulimb => wrapping_ulimb_i64,
    overflowing_ulimb => overflowing_ulimb_i64,
    wrapping_ilimb => wrapping_ilimb_i64,
    overflowing_ilimb => overflowing_ilimb_i64,
    wrapping_uwide => wrapping_uwide_i64,
    overflowing_uwide => overflowing_uwide_i64,
    wrapping_iwide => wrapping_iwide_i64,
    overflowing_iwide => overflowing_iwide_i64,
    carrying => carrying_add_u64,
);

limb_function!(wrapping_signed, wrapping_i64, wrapping_i32, &[ULimb; N], ret => [ULimb; N]);
limb_function!(overflowing_signed, overflowing_i64, overflowing_i32, &[ULimb; N], &[ULimb; N], ret => ([ULimb; N], bool));

// limb
limb_function!(wrapping_ulimb, wrapping_ulimb_i64, wrapping_ulimb_i32, &[ULimb; N], ULimb, ret => [ULimb; N]);
limb_function!(wrapping_ilimb, wrapping_ilimb_i64, wrapping_ilimb_i32, &[ULimb; N], ILimb, ret => [ULimb; N]);
limb_function!(overflowing_ulimb, overflowing_ulimb_i64, overflowing_ulimb_i32, &[ULimb; N], ULimb, ret => ([ULimb; N], bool));
limb_function!(overflowing_ilimb, overflowing_ilimb_i64, overflowing_ilimb_i32, &[ULimb; N], ILimb, ret => ([ULimb; N], bool));

// wide
limb_function!(wrapping_uwide, wrapping_uwide_i64, wrapping_uwide_i32, &[ULimb; N], UWide, ret => [ULimb; N]);
limb_function!(wrapping_iwide, wrapping_iwide_i64, wrapping_iwide_i32, &[ULimb; N], IWide, ret => [ULimb; N]);
limb_function!(overflowing_uwide, overflowing_uwide_i64, overflowing_uwide_i32, &[ULimb; N], UWide, ret => ([ULimb; N], bool));
limb_function!(overflowing_iwide, overflowing_iwide_i64, overflowing_iwide_i32, &[ULimb; N], IWide, ret => ([ULimb; N], bool));

#[cfg(test)]
mod tests {
    use super::*;

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

    #[test]
    fn overflowing_add_u32_test() {
        assert_eq!(from_le_over(&[1, 0], &[1, 0], overflowing_u32), ([2, 0], false));
        assert_eq!(
            from_le_over(&[u32::MAX, 0], &[u32::MAX, 0], overflowing_u32),
            ([u32::MAX - 1, 1], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, 1], &[u32::MAX, 0], overflowing_u32),
            ([u32::MAX - 1, 2], false)
        );
        assert_eq!(from_le_over(&[u32::MAX, u32::MAX], &[1, 0], overflowing_u32), ([0, 0], true));
        assert_eq!(from_le_over(&[u32::MAX, u32::MAX], &[2, 0], overflowing_u32), ([1, 0], true));
        assert_eq!(
            from_le_over(&[u32::MAX, u32::MAX], &[u32::MAX, u32::MAX], overflowing_u32),
            ([u32::MAX - 1, u32::MAX], true)
        );
    }

    #[test]
    fn overflowing_add_i32_test() {
        assert_eq!(from_le_over(&[1, 0], &[1, 0], overflowing_i32), ([2, 0], false));
        assert_eq!(
            from_le_over(&[u32::MAX, 0], &[u32::MAX, 0], overflowing_i32),
            ([u32::MAX - 1, 1], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, 1], &[u32::MAX, 0], overflowing_i32),
            ([u32::MAX - 1, 2], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, i32::MAX as u32], &[1, 0], overflowing_i32),
            ([0, i32::MIN as u32], true)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, i32::MAX as u32], &[2, 0], overflowing_i32),
            ([1, i32::MIN as u32], true)
        );
        assert_eq!(
            from_le_over(
                &[u32::MAX, i32::MAX as u32],
                &[u32::MAX, i32::MAX as u32],
                overflowing_i32
            ),
            ([u32::MAX - 1, -1i32 as u32], true)
        );
    }
}
