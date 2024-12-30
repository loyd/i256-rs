//! Const implementations of subtraction.

use super::bigint::*;
use crate::{ILimb, ULimb};

macro_rules! unsigned_define {
    (
        $u:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_limb =>
        $wrapping_limb:ident,overflowing_limb =>
        $overflowing_limb:ident,borrowing =>
        $borrowing:ident $(,)?
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
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            let mut vi: $u;
            while index < N - 1 {
                (vi, c) = $borrowing(ne_index!(x[index]), ne_index!(y[index]), c);
                ne_index!(result[index] = vi);
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
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            let mut vi: $u;
            while index < N - 1 {
                (vi, c) = $borrowing(ne_index!(x[index]), ne_index!(y[index]), c);
                ne_index!(result[index] = vi);
                index += 1;
            }

            let (vn, c) = $borrowing(ne_index!(x[index]), ne_index!(y[index]), c);
            ne_index!(result[index] = vn);

            (result, c)
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

unsigned_define!(
    u32,
    wrapping_full => wrapping_u32,
    overflowing_full => overflowing_u32,
    wrapping_limb => wrapping_limb_u32,
    overflowing_limb => overflowing_limb_u32,
    borrowing => borrowing_sub_u32,
);
unsigned_define!(
    u64,
    wrapping_full => wrapping_u64,
    overflowing_full => overflowing_u64,
    wrapping_limb => wrapping_limb_u64,
    overflowing_limb => overflowing_limb_u64,
    borrowing => borrowing_sub_u64,
);

limb_function!(wrapping_unsigned, wrapping_u64, wrapping_u32, &[ULimb; N], ret => [ULimb; N]);
limb_function!(overflowing_unsigned, overflowing_u64, overflowing_u32, &[ULimb; N], &[ULimb; N], ret => ([ULimb; N], bool));

limb_function!(wrapping_limb, wrapping_limb_u64, wrapping_limb_u32, &[ULimb; N], ULimb, ret => [ULimb; N]);
limb_function!(overflowing_limb, overflowing_limb_u64, overflowing_limb_u32, &[ULimb; N], ULimb, ret => ([ULimb; N], bool));

macro_rules! signed_define {
    (
        $u:ty,
        $s:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_ulimb =>
        $wrapping_ulimb:ident,overflowing_ulimb =>
        $overflowing_ulimb:ident,wrapping_ilimb =>
        $wrapping_ilimb:ident,overflowing_ilimb =>
        $overflowing_ilimb:ident,borrowing =>
        $borrowing:ident $(,)?
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
            assert!(<$u>::BITS == <$s>::BITS);
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            let mut vi: $u;
            while index < N - 1 {
                (vi, c) = $borrowing(ne_index!(x[index]), ne_index!(y[index]), c);
                ne_index!(result[index] = vi);
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
            assert!(<$u>::BITS == <$s>::BITS);
            assert!(N >= 2);

            let mut index = 0;
            let mut result = [0; N];
            let mut c: bool = false;
            let mut vi: $u;
            while index < N - 1 {
                (vi, c) = $borrowing(ne_index!(x[index]), ne_index!(y[index]), c);
                ne_index!(result[index] = vi);
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

signed_define!(
    u32,
    i32,
    wrapping_full => wrapping_i32,
    overflowing_full => overflowing_i32,
    wrapping_ulimb => wrapping_ulimb_i32,
    overflowing_ulimb => overflowing_ulimb_i32,
    wrapping_ilimb => wrapping_ilimb_i32,
    overflowing_ilimb => overflowing_ilimb_i32,
    borrowing => borrowing_sub_u32,
);
signed_define!(
    u64,
    i64,
    wrapping_full => wrapping_i64,
    overflowing_full => overflowing_i64,
    wrapping_ulimb => wrapping_ulimb_i64,
    overflowing_ulimb => overflowing_ulimb_i64,
    wrapping_ilimb => wrapping_ilimb_i64,
    overflowing_ilimb => overflowing_ilimb_i64,
    borrowing => borrowing_sub_u64,
);

limb_function!(wrapping_signed, wrapping_i64, wrapping_i32, &[ULimb; N], ret => [ULimb; N]);
limb_function!(overflowing_signed, overflowing_i64, overflowing_i32, &[ULimb; N], &[ULimb; N], ret => ([ULimb; N], bool));

limb_function!(wrapping_ulimb, wrapping_ulimb_i64, wrapping_ulimb_i32, &[ULimb; N], ULimb, ret => [ULimb; N]);
limb_function!(wrapping_ilimb, wrapping_ilimb_i64, wrapping_ilimb_i32, &[ULimb; N], ILimb, ret => [ULimb; N]);
limb_function!(overflowing_ulimb, overflowing_ulimb_i64, overflowing_ulimb_i32, &[ULimb; N], ULimb, ret => ([ULimb; N], bool));
limb_function!(overflowing_ilimb, overflowing_ilimb_i64, overflowing_ilimb_i32, &[ULimb; N], ILimb, ret => ([ULimb; N], bool));

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
    fn overflowing_sub_u32_test() {
        assert_eq!(from_le_over(&[0, 0], &[1, 0], overflowing_u32), ([u32::MAX, u32::MAX], true));
        assert_eq!(from_le_over(&[1, 0], &[1, 0], overflowing_u32), ([0, 0], false));
        assert_eq!(from_le_over(&[1, 0], &[0, 0], overflowing_u32), ([1, 0], false));
        assert_eq!(
            from_le_over(&[u32::MAX, 1], &[0, 2], overflowing_u32),
            ([u32::MAX, u32::MAX], true)
        );
        assert_eq!(from_le_over(&[0, 1], &[0, 2], overflowing_u32), ([0, 4294967295], true));
        assert_eq!(from_le_over(&[0, 1], &[1, 1], overflowing_u32), ([u32::MAX, u32::MAX], true));
    }
}
