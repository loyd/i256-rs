//! Arithmetic utilities from small, native integer components.
//!
//! This allows the construction of larger type sizes from native,
//! fast integers.

#![doc(hidden)]
#![allow(clippy::useless_transmute)]

use core::mem;

// NOTE: These are named after the size of the types that are the
// operands: for example, `wrapping_add_u8` takes 2x `u8`, so it's
// a 16-bit addition.

// NOTE: Division and remainders aren't supported due to the difficulty in
// implementation. See `div.rs` for the implementation.

// Utility to split a value into low and high bits.
// This also includes a variety to split into arrays.
#[macro_export]
macro_rules! split {
    ($u:ty, $h:ty, $v:expr) => {{
        // FIXME: Using raw transmutes can allow vectorizing,
        // restore to raw splits when possible.
        //  let (lo, hi) = split!($u, $h, $v);
        //  [lo, hi]
        let bytes = $v.to_le_bytes();
        // SAFETY: safe since this is plain old data
        let v: [$h; 2] = unsafe { mem::transmute(bytes) };
        v
    }};

    ($u:ty, $h:ty, $x:expr, $y:expr) => {{
        // FIXME: Using raw transmutes can allow vectorizing,
        // restore to raw splits when possible.
        //  let (x0, x1) = split!($u, $h, $x);
        //  let (y0, y1) = split!($u, $h, $y);
        //  [x0, x1, y0, y1]
        let xb = $x.to_le_bytes();
        let yb = $y.to_le_bytes();
        // SAFETY: safe since this is plain old data
        let v: [$h; 4] = unsafe { mem::transmute([xb, yb]) };
        v
    }};
}

// Unsplit our array and shift bytes into place.
#[macro_export]
macro_rules! unsplit {
    (@wrapping $u:ty, $v:expr, $shift:expr) => {{
        let r = $v;
        let lo = ((r[1] as $u) << $shift) | (r[0] as $u);
        let hi = ((r[3] as $u) << $shift) | (r[2] as $u);
        (lo, hi)
    }};

    (@overflow $u:ty, $v:expr, $shift:expr) => {{
        let (r, o) = $v;
        let lo = ((r[1] as $u) << $shift) | (r[0] as $u);
        let hi = ((r[3] as $u) << $shift) | (r[2] as $u);
        (lo, hi, o)
    }};
}

pub(crate) use split;
pub(crate) use unsplit;

// BINARY OPS - UNSIGNED
// ---------------------

macro_rules! add_unsigned_impl {
    (
        $u:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_wide =>
        $wrapping_wide:ident,overflowing_wide =>
        $overflowing_wide:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_add` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 128-bit addition (2x u64 + 2x u64), it optimizes to 1
        /// `add` and 1 `adc` instruction.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     add     rax, rdx
        ///     adc     rsi, rcx
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 2
        /// `add` and 4 `adc` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     add     rcx, qword ptr [rsp + 24]
        ///     adc     r8, qword ptr [rsp + 32]
        ///     add     rsi, qword ptr [rsp + 8]
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     mov     rax, rdi
        ///     adc     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_full(x0: $u, x1: $u, y0: $u, y1: $u) -> ($u, $u) {
            // NOTE: This is significantly slower than implementing with overflowing.
            let (v0, c0) = x0.overflowing_add(y0);
            let v1 = x1.wrapping_add(y1);
            let v1 = v1.wrapping_add(c0 as $u);
            (v0, v1)
        }

        /// Const implementation of `overflowing_add` for internal algorithm use.
        ///
        /// Returns the value and if the add overflowed. In practice,
        /// the nightly (carrying) and the overflowing add variants
        /// have the same ASM generated, but this might not be the
        /// case in the future or for different architectures.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 128-bit addition (2x u64 + 2x u64), it optimizes to 1
        /// `add`, 1 `adc`, and 1 `set` instruction.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     add     rsi, rcx
        ///     adc     rdx, r8
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     setb    byte ptr [rdi + 16]
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 2
        /// `add`, 4 `adc`, 2 `set` and 1 `or` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, qword ptr [rsp + 24]
        ///     add     rax, rcx
        ///     mov     rax, qword ptr [rsp + 32]
        ///     adc     rax, r8
        ///     setb    r9b
        ///     add     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     adc     r8, 0
        ///     setb    dil
        ///     or      dil, r9b
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], r8
        ///     mov     byte ptr [rax + 32], dil
        ///     ret
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_full(x0: $u, x1: $u, y0: $u, y1: $u) -> ($u, $u, bool) {
            let (v0, c0) = x0.overflowing_add(y0);
            // FIXME: Move to `carrying_add` once stable.
            let (v1, c1) = x1.overflowing_add(y1);
            let (v1, c2) = v1.overflowing_add(c0 as $u);

            (v0, v1, c1 | c2)
        }

        /// Const implementation of `wrapping_add` a small number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small value.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 128-bit addition (2x u64 + 2x u64), it optimizes to 1
        /// `add` and 1 `adc` instruction.
        ///
        /// ```asm
        /// wrapping_add:
        ///    mov     rax, rdi
        ///    add     rax, rdx
        ///    adc     rsi, 0
        ///    mov     rdx, rsi
        ///    ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 1
        /// `add` and 3 `adc` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///    add     rsi, qword ptr [rsp + 8]
        ///    adc     rdx, qword ptr [rsp + 16]
        ///    adc     rcx, 0
        ///    mov     rax, rdi
        ///    adc     r8, 0
        ///    mov     qword ptr [rdi], rsi
        ///    mov     qword ptr [rdi + 8], rdx
        ///    mov     qword ptr [rdi + 16], rcx
        ///    mov     qword ptr [rdi + 24], r8
        ///    ret
        /// ```
        #[inline]
        pub const fn $wrapping_wide(x0: $u, x1: $u, y: $u) -> ($u, $u) {
            // NOTE: This is significantly slower than implementing with overflowing.
            let (v0, c0) = x0.overflowing_add(y);
            let v1 = x1.wrapping_add(c0 as $u);
            (v0, v1)
        }

        /// Const implementation of `overflowing_add` a small number to the wider type.
        ///
        /// Returns the value, wrapping on overflow, and if the add overflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small value.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 128-bit addition (2x u64 + 2x u64), it optimizes to 1
        /// `add`, 1 `adc`, and 1 `set` instruction.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     add     rsi, rcx
        ///     adc     rdx, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     setb    byte ptr [rdi + 16]
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 1
        /// `add`, 3 `adc`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     add     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     adc     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     setb    byte ptr [rdi + 32]
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_wide(x0: $u, x1: $u, y: $u) -> ($u, $u, bool) {
            let (v0, c0) = x0.overflowing_add(y);
            let (v1, c1) = x1.overflowing_add(c0 as $u);
            (v0, v1, c1)
        }
    };
}

add_unsigned_impl!(
    u8,
    wrapping_full => wrapping_add_u8,
    overflowing_full => overflowing_add_u8,
    wrapping_wide => wrapping_add_wide_u8,
    overflowing_wide => overflowing_add_wide_u8
);
add_unsigned_impl!(
    u16,
    wrapping_full => wrapping_add_u16,
    overflowing_full => overflowing_add_u16,
    wrapping_wide => wrapping_add_wide_u16,
    overflowing_wide => overflowing_add_wide_u16
);
add_unsigned_impl!(
    u32,
    wrapping_full => wrapping_add_u32,
    overflowing_full => overflowing_add_u32,
    wrapping_wide => wrapping_add_wide_u32,
    overflowing_wide => overflowing_add_wide_u32
);
add_unsigned_impl!(
    u64,
    wrapping_full => wrapping_add_u64,
    overflowing_full => overflowing_add_u64,
    wrapping_wide => wrapping_add_wide_u64,
    overflowing_wide => overflowing_add_wide_u64
);
add_unsigned_impl!(
    u128,
    wrapping_full => wrapping_add_u128,
    overflowing_full => overflowing_add_u128,
    wrapping_wide => wrapping_add_wide_u128,
    overflowing_wide => overflowing_add_wide_u128
);

macro_rules! sub_unsigned_impl {
    (
        $u:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_wide =>
        $wrapping_wide:ident,overflowing_wide =>
        $overflowing_wide:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_sub` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 128-bit addition (2x u64 + 2x u64), it optimizes to 1
        /// `sub` and 1 `sbb` instruction.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, rdi
        ///     sub     rax, rdx
        ///     sbb     rsi, rcx
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit subtraction (2x u128 + 2x u128), it optimizes to 2
        /// `sub` and 4 `sbb` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     sub     rcx, qword ptr [rsp + 24]
        ///     sbb     r8, qword ptr [rsp + 32]
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     mov     rax, rdi
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_full(x0: $u, x1: $u, y0: $u, y1: $u) -> ($u, $u) {
            let (v0, c0) = x0.overflowing_sub(y0);
            let v1 = x1.wrapping_sub(y1);
            let v1 = v1.wrapping_sub(c0 as $u);
            (v0, v1)
        }

        /// Const implementation of `overflowing_sub` for internal algorithm use.
        ///
        /// Returns the value and if the sub underflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 128-bit subtraction (2x u64 + 2x u64), it optimizes to 1
        /// `sub`, 1 `sbb`, and 1 `set` instruction.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     sub     rsi, rcx
        ///     sbb     rdx, r8
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     setb    byte ptr [rdi + 16]
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit subtraction (2x u128 + 2x u128), it optimizes to 2
        /// `sub`, 4 `sbb`, 2 `set`, and 1 `or` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     sub     rcx, qword ptr [rsp + 24]
        ///     sbb     r8, qword ptr [rsp + 32]
        ///     setb    r9b
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     sbb     r8, 0
        ///     setb    dil
        ///     or      dil, r9b
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], r8
        ///     mov     byte ptr [rax + 32], dil
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_full(x0: $u, x1: $u, y0: $u, y1: $u) -> ($u, $u, bool) {
            // NOTE: When we ignore the carry in the caller, this optimizes the same.
            let (v0, c0) = x0.overflowing_sub(y0);
            // FIXME: Move to `borrowing_sub` once stable.
            let (v1, c1) = x1.overflowing_sub(y1);
            let (v1, c2) = v1.overflowing_sub(c0 as $u);

            (v0, v1, c1 | c2)
        }

        /// Const implementation of `wrapping_sub` a small number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small value.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 128-bit addition (2x u64 + 2x u64), it optimizes to 1
        /// `sub` and 1 `sbb` instruction.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, rdi
        ///     sub     rax, rdx
        ///     sbb     rsi, 0
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 128-bit subtraction (2x u128 + 2x u128), it optimizes to 1
        /// `sub` and 3 `sbb` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     mov     rax, rdi
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_wide(x0: $u, x1: $u, y: $u) -> ($u, $u) {
            let (v0, c0) = x0.overflowing_sub(y);
            let v1 = x1.wrapping_sub(c0 as $u);
            (v0, v1)
        }

        /// Const implementation to subtract a small number from the wider type.
        ///
        /// Returns the value and if the sub overflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small value.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 128-bit subtraction (2x u64 + 2x u64), it optimizes to 1
        /// `sub`, 1 `sbb`, and 1 `set` instruction.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     sub     rsi, rcx
        ///     sbb     rdx, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     setb    byte ptr [rdi + 16]
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 128-bit subtraction (2x u128 + 2x u128), it optimizes to 1
        /// `sub`, 3 `sbb`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     setb    byte ptr [rdi + 32]
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_wide(x0: $u, x1: $u, y: $u) -> ($u, $u, bool) {
            // NOTE: When we ignore the carry in the caller, this optimizes the same.
            // This is super efficient, it becomes an `add` and an `adc` (add carry).
            let (v0, c0) = x0.overflowing_sub(y);
            let (v1, c1) = x1.overflowing_sub(c0 as $u);
            (v0, v1, c1)
        }
    };
}

sub_unsigned_impl!(
    u8,
    wrapping_full => wrapping_sub_u8,
    overflowing_full => overflowing_sub_u8,
    wrapping_wide => wrapping_sub_wide_u8,
    overflowing_wide => overflowing_sub_wide_u8
);
sub_unsigned_impl!(
    u16,
    wrapping_full => wrapping_sub_u16,
    overflowing_full => overflowing_sub_u16,
    wrapping_wide => wrapping_sub_wide_u16,
    overflowing_wide => overflowing_sub_wide_u16
);
sub_unsigned_impl!(
    u32,
    wrapping_full => wrapping_sub_u32,
    overflowing_full => overflowing_sub_u32,
    wrapping_wide => wrapping_sub_wide_u32,
    overflowing_wide => overflowing_sub_wide_u32
);
sub_unsigned_impl!(
    u64,
    wrapping_full => wrapping_sub_u64,
    overflowing_full => overflowing_sub_u64,
    wrapping_wide => wrapping_sub_wide_u64,
    overflowing_wide => overflowing_sub_wide_u64
);
sub_unsigned_impl!(
    u128,
    wrapping_full => wrapping_sub_u128,
    overflowing_full => overflowing_sub_u128,
    wrapping_wide => wrapping_sub_wide_u128,
    overflowing_wide => overflowing_sub_wide_u128
);

macro_rules! mul_unsigned_impl {
    (
        full => $u:ty,
        half => $h:ty,
        wrapping_array => $wrapping_array:ident,
        wrapping_full => $wrapping_full:ident,
        wrapping_wide => $wrapping_wide:ident,
        wrapping_limb => $wrapping_limb:ident,
        overflowing_array => $overflowing_array:ident,
        overflowing_full => $overflowing_full:ident,
        overflowing_wide => $overflowing_wide:ident,
        overflowing_limb => $overflowing_limb:ident $(,)?
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
        /// * `x` - The multiplier.
        /// * `y` - The multiplicand.
        ///
        /// Returns the low and high bits, in that order.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $wrapping_array<const M: usize, const N: usize>(x: &[$h; M], y: &[$h; N]) -> [$h; M] {
            // NOTE: This assumes our multiplier is at least the multiplicand
            // dimensions, so we can just invert it in the other case.
            assert!(M >= N, "lhs must be >= than rhs");

            const SHIFT: u32 = <$h>::BITS;
            let mut r: [$h; M] = [0; M];
            let mut carry: $h;

            // this is effectively an 2D matrix for long multiplication.
            let mut i: usize = 0;
            let mut j: usize;
            while i < M {
                carry = 0;
                j = 0;
                // NOTE: This is likely due to a miscompilation but this
                // is significantly faster than indexing within the loop
                // on `x86_64`.
                let xi = x[i];
                while j < N {
                    // NOTE: This repeats but it keeps the previous result
                    // `r[ij]` as current.
                    let ij = i + j;
                    let yj = y[j];
                    if ij < M {
                        // FIXME: Replace with `carrying_mul` when we add it
                        let full = (xi as $u) * (yj as $u);
                        let prod = carry as $u + r[ij] as $u + full;
                        r[ij] = prod as $h;
                        carry = (prod >> SHIFT) as $h;
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
                    r[i + N] = carry;
                }
                i += 1;
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
        /// item: rather than using 4 limbs, if we're multiplying `(u128, u128) * u128`,
        /// we can use 2 limbs for the right operand, and for `(u128, u128) * u64`, only
        /// 1 limb.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
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
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $wrapping_full(x0: $u, x1: $u, y0: $u, y1: $u) -> ($u, $u) {
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
            let x = split!($u, $h, x0, x1);
            let y = split!($u, $h, y0, y1);
            let r = $wrapping_array(&x, &y);
            unsplit!(@wrapping $u, r, <$h>::BITS)
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
        /// item: rather than using 4 limbs, if we're multiplying `(u128, u128) * u128`,
        /// we can use 2 limbs for the right operand, and for `(u128, u128) * u64`, only
        /// 1 limb.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - A small, unsigned factor to multiply by.
        ///
        /// This multiplies a wide value, say, an `u64` as `(u32, u32)`
        /// pairs by a small value (`u32`) which can add optimizations
        /// for scalar word processing.
        ///
        /// # Assembly
        ///
        /// Using algorithm (3), the addition of `(u128, u128) + (u128, u128)` is in the
        /// worst case 10 `mul` and 15 `add` instructions, while `(u128, u128) + u128`
        /// is at worst 8 `mul` and 12 `add` instructions, which optimizes quite nicely.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $wrapping_wide(x0: $u, x1: $u, y: $u) -> ($u, $u) {
            // 256-Bit
            // -------
            // wrapping_mul_wide_u128:
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
            let x = split!($u, $h, x0, x1);
            let y = split!($u, $h, y);
            let r = $wrapping_array(&x, &y);
            unsplit!(@wrapping $u, r, <$h>::BITS)
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
        /// item: rather than using 4 limbs, if we're multiplying `(u128, u128) * u128`,
        /// we can use 2 limbs for the right operand, and for `(u128, u128) * u64`, only
        /// 1 limb.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - A small, unsigned factor to multiply by.
        ///
        /// Using algorithm (3), the addition of `(u128, u128) + (u128, u128)` is in the
        /// worst case 10 `mul` and 15 `add` instructions, while `(u128, u128) + u64`
        /// is always 4 `mul` and 3 `add` instructions without any branching. This is
        /// extremely efficient.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $wrapping_limb(x0: $u, x1: $u, y: $h) -> ($u, $u) {
            // 256-Bit
            // -------
            // wrapping_mul_limb_u128:
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
            let x = split!($u, $h, x0, x1);
            let y = [y];
            let r = $wrapping_array(&x, &y);
            unsplit!(@wrapping $u, r, <$h>::BITS)
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
        /// * `x` - The multiplier.
        /// * `y` - The multiplicand.
        ///
        /// Returns the low and high bits, in that order.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $overflowing_array<const M: usize, const N: usize>(x: &[$h; M], y: &[$h; N]) -> ([$h; M], bool) {
            // NOTE: This assumes our multiplier is at least the multiplicand
            // dimensions, so we can just invert it in the other case.
            assert!(M >= N, "lhs must be >= than rhs");

            const SHIFT: u32 = <$h>::BITS;
            let mut r: [$h; M] = [0; M];
            let mut carry: $h;
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
                let xi = x[i];
                while j < N {
                    let ij = i + j;
                    let yj = y[j];
                    if ij < M {
                        // FIXME: Replace with `carrying_mul` when we add it
                        let full = (xi as $u) * (yj as $u);
                        let prod = carry as $u + r[ij] as $u + full;
                        r[ij] = prod as $h;
                        carry = (prod >> SHIFT) as $h;
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
                    r[i + N] = carry;
                } else if carry != 0 {
                    overflowed = true;
                }
                i += 1;
            }

            (r, overflowed)
        }

        /// Const implementation of `wrapping_mul` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow and if the result overflowed.
        ///
        /// Many different algorithms were attempted, with a soft [`mulx`] approach (1),
        /// a flat, fixed-width long multiplication (2), and a short-circuiting long
        /// multiplication (3). Algorithm (3) had the best performance for 128-bit
        /// multiplication, however, algorithm (1) was better for smaller type sizes.
        ///
        /// This also optimized much better when multiplying by a single or a half-sized
        /// item: rather than using 4 limbs, if we're multiplying `(u128, u128) * u128`,
        /// we can use 2 limbs for the right operand, and for `(u128, u128) * u64`, only
        /// 1 limb.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// The analysis here is practically identical to that of `wrapping_full`.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $overflowing_full(x0: $u, x1: $u, y0: $u, y1: $u) -> ($u, $u, bool) {
            let x = split!($u, $h, x0, x1);
            let y = split!($u, $h, y0, y1);
            let r = $overflowing_array(&x, &y);
            unsplit!(@overflow $u, r, <$h>::BITS)
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
        /// item: rather than using 4 limbs, if we're multiplying `(u128, u128) * u128`,
        /// we can use 2 limbs for the right operand, and for `(u128, u128) * u64`, only
        /// 1 limb.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - A small, unsigned factor to multiply by.
        ///
        /// This multiplies a wide value, say, an `u64` as `(u32, u32)` pairs by a small
        /// value (`u32`) which can add optimizations for scalar word processing.
        ///
        /// # Assembly
        ///
        /// The analysis here is practically identical to that of `wrapping_wide`.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $overflowing_wide(x0: $u, x1: $u, y: $u) -> ($u, $u, bool) {
            let x = split!($u, $h, x0, x1);
            let y = split!($u, $h, y);
            let r = $overflowing_array(&x, &y);
            unsplit!(@overflow $u, r, <$h>::BITS)
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
        /// item: rather than using 4 limbs, if we're multiplying `(u128, u128) * u128`,
        /// we can use 2 limbs for the right operand, and for `(u128, u128) * u64`, only
        /// 1 limb.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - A small, unsigned factor to multiply by.
        ///
        /// # Assembly
        ///
        /// The analysis here is practically identical to that of `wrapping_limb`.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $overflowing_limb(x0: $u, x1: $u, y: $h) -> ($u, $u, bool) {
            let x = split!($u, $h, x0, x1);
            let r = $overflowing_array(&x, &[y]);
            unsplit!(@overflow $u, r, <$h>::BITS)
        }
    };
}

// NOTE: We can't use a half size for `u8` and `usize` is variable
// width and since they're only exposed for testing we don't care.
mul_unsigned_impl!(
    full => u16,
    half => u8,
    wrapping_array => wrapping_mul_arr_u16,
    wrapping_full => wrapping_mul_u16,
    wrapping_wide => wrapping_mul_wide_u16,
    wrapping_limb => wrapping_mul_limb_u16,
    overflowing_array => overflowing_mul_arr_u16,
    overflowing_full => overflowing_mul_u16,
    overflowing_wide => overflowing_mul_wide_u16,
    overflowing_limb => overflowing_mul_limb_u16,
);
mul_unsigned_impl!(
    full => u32,
    half => u16,
    wrapping_array => wrapping_mul_arr_u32,
    wrapping_full => wrapping_mul_u32,
    wrapping_wide => wrapping_mul_wide_u32,
    wrapping_limb => wrapping_mul_limb_u32,
    overflowing_array => overflowing_mul_arr_u32,
    overflowing_full => overflowing_mul_u32,
    overflowing_wide => overflowing_mul_wide_u32,
    overflowing_limb => overflowing_mul_limb_u32,
);
mul_unsigned_impl!(
    full => u64,
    half => u32,
    wrapping_array => wrapping_mul_arr_u64,
    wrapping_full => wrapping_mul_u64,
    wrapping_wide => wrapping_mul_wide_u64,
    wrapping_limb => wrapping_mul_limb_u64,
    overflowing_array => overflowing_mul_arr_u64,
    overflowing_full => overflowing_mul_u64,
    overflowing_wide => overflowing_mul_wide_u64,
    overflowing_limb => overflowing_mul_limb_u64,
);
mul_unsigned_impl!(
    full => u128,
    half => u64,
    wrapping_array => wrapping_mul_arr_u128,
    wrapping_full => wrapping_mul_u128,
    wrapping_wide => wrapping_mul_wide_u128,
    wrapping_limb => wrapping_mul_limb_u128,
    overflowing_array => overflowing_mul_arr_u128,
    overflowing_full => overflowing_mul_u128,
    overflowing_wide => overflowing_mul_wide_u128,
    overflowing_limb => overflowing_mul_limb_u128,
);

macro_rules! swap_unsigned_impl {
    ($($u:ty => $swap_bytes:ident, $reverse_bits:ident,)*) => ($(
        /// Reverses the byte order of the integer.
        ///
        /// # Assembly
        ///
        /// This optimizes very nicely, with efficient `bswap` or `rol`
        /// implementations for each.
        #[inline(always)]
        pub const fn $swap_bytes(x0: $u, x1: $u) -> ($u, $u) {
            (x1.swap_bytes(), x0.swap_bytes())
        }

        /// Reverses the order of bits in the integer.
        ///
        /// The least significant bit becomes the most significant bit, second
        /// least-significant bit becomes second most-significant bit, etc.
        /// Reversing bits is also quite inefficient, and for 128-bit and
        /// larger integers (2x `u64`), this is just as efficient as the
        /// native implementation. For smaller type sizes, the compiler can
        /// optimize the implementation, but we go beyond that realm.
        #[inline(always)]
        pub const fn $reverse_bits(x0: $u, x1: $u) -> ($u, $u) {
            (x1.reverse_bits(), x0.reverse_bits())
        }
    )*);
}

swap_unsigned_impl! {
    u8 => swap_bytes_u8, reverse_bits_u8,
    u16 => swap_bytes_u16, reverse_bits_u16,
    u32 => swap_bytes_u32, reverse_bits_u32,
    u64 => swap_bytes_u64, reverse_bits_u64,
    u128 => swap_bytes_u128, reverse_bits_u128,
}

macro_rules! shift_unsigned_impl {
    ($($u:ty => $shl:ident, $shr:ident,)*) => ($(
        /// Const implementation of `Shl` for internal algorithm use.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `shift` - The number of bits to shift.
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
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `shift` - The number of bits to shift.
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
    u8 => shl_u8, shr_u8,
    u16 => shl_u16, shr_u16,
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
    u8 => rotate_left_u8, rotate_right_u8,
    u16 => rotate_left_u16, rotate_right_u16,
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
    u8,
    i8,
    as_uwide => as_uwide_u8,
    as_unarrow => as_unarrow_u8,
    as_iwide => as_iwide_u8,
    as_inarrow => as_inarrow_u8,
    wide_cast => wide_cast_u8
);
unsigned_primitive_cast!(
    u16,
    i16,
    as_uwide => as_uwide_u16,
    as_unarrow => as_unarrow_u16,
    as_iwide => as_iwide_u16,
    as_inarrow => as_inarrow_u16,
    wide_cast => wide_cast_u16
);
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
        $overflowing_full:ident,wrapping_uwide =>
        $wrapping_uwide:ident,overflowing_uwide =>
        $overflowing_uwide:ident,wrapping_iwide =>
        $wrapping_iwide:ident,overflowing_iwide =>
        $overflowing_iwide:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_add` for internal algorithm use.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on `x86_64`, for a
        /// 128-bit addition (1x u64, 1x i64 + 1x u64), it optimizes
        /// to 1 `add`, and 1 `adc` instruction.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     add     rax, rdx
        ///     adc     rsi, rcx
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes very well, for example, on `x86_64`,
        /// for a 256-bit addition (1x u128, 1x i128 + x u64), it
        /// optimizes to 2 `add` and 4 `adc` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     add     rcx, qword ptr [rsp + 24]
        ///     adc     r8, qword ptr [rsp + 32]
        ///     add     rsi, qword ptr [rsp + 8]
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     mov     rax, rdi
        ///     adc     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_full(x0: $u, x1: $s, y0: $u, y1: $s) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let (v0, c0) = x0.overflowing_add(y0);
            let v1 = x1.wrapping_add(y1);
            let v1 = v1.wrapping_add(c0 as $s);
            (v0, v1)
        }

        /// Const implementation of `overflowing_add` for internal algorithm use.
        ///
        /// Returns the value and if the add overflowed. In practice,
        /// the nightly (carrying) and the overflowing add variants
        /// have the same ASM generated, but this might not be the
        /// case in the future or for different architectures.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 128-bit addition (1x u64, 1x i64 + 1x u64, 1x u64),
        /// it optimizes to 2
        /// `add`, 1 `adc`, 2 `set`, and 1 `or` instruction.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     add     rdx, r8
        ///     seto    dil
        ///     add     rsi, rcx
        ///     adc     rdx, 0
        ///     seto    cl
        ///     or      cl, dil
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     byte ptr [rax + 16], cl
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit addition (2x u128 + 2x u128), it optimizes to 2
        /// `add`, 4 `adc`, 2 `set` and 1 `or` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     add     rcx, qword ptr [rsp + 24]
        ///     adc     r8, qword ptr [rsp + 32]
        ///     seto    r9b
        ///     add     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     adc     r8, 0
        ///     seto    dil
        ///     or      dil, r9b
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], r8
        ///     mov     byte ptr [rax + 32], dil
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_full(x0: $u, x1: $s, y0: $u, y1: $s) -> ($u, $s, bool) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let (v0, c0) = x0.overflowing_add(y0);
            // FIXME: Move to `carrying_add` once stable.
            let (v1, c1) = x1.overflowing_add(y1);
            let (v1, c2) = v1.overflowing_add(c0 as $s);

            (v0, v1, c1 | c2)
        }

        /// Const implementation to add a small, unsigned number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, unsigned value.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on `x86_64`, for a
        /// 128-bit addition (1x u64, 1x i64 + 1x u64), it optimizes
        /// to 1 `add`, and 1 `adc` instruction.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     add     rax, rdx
        ///     adc     rsi, 0
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes fairly well, for example, on `x86_64`,
        /// for a 256-bit addition (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `add` and 3 `adc` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     add     rsi, qword ptr [rsp + 8]
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     mov     rax, rdi
        ///     adc     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_uwide(x0: $u, x1: $s, y: $u) -> ($u, $s) {
            let (v0, c0) = x0.overflowing_add(y);
            let v1 = x1.wrapping_add(c0 as $s);
            (v0, v1)
        }

        /// Const implementation to add a small, unsigned number to the wider type.
        ///
        /// Returns the value and if the add overflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, unsigned value.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on `x86_64`, for a
        /// 128-bit addition (1x u64, 1x i64 + 1x u64), it optimizes
        /// to 1 `add`, 1 `adc`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     add     rsi, rcx
        ///     adc     rdx, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     seto    byte ptr [rdi + 16]
        ///     ret
        /// ```
        ///
        /// This optimizes fairly well, for example, on `x86_64`,
        /// for a 256-bit addition (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `add`, 3 `adc`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     add     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     adc     rdx, qword ptr [rsp + 16]
        ///     adc     rcx, 0
        ///     adc     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     seto    byte ptr [rdi + 32]
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_uwide(x0: $u, x1: $s, y: $u) -> ($u, $s, bool) {
            let (v0, c0) = x0.overflowing_add(y);
            let (v1, c1) = x1.overflowing_add(c0 as $s);
            (v0, v1, c1)
        }

        /// Const implementation to add a small, signed number to the wider type.
        ///
        /// Returns the value, wrapping on overflow. This is effectively the
        /// implementation of the wider type, just with an extra bitshift to expand
        /// the type to the wider width.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, unsigned value.
        ///
        /// # Assembly
        ///
        /// This optimizes well, for example, on `x86_64`,
        /// for a 128-bit addition (1x u64, 1x i64 + 1x i64), it
        /// optimizes to 1 `add`, 1 `adc`, and 1 `sar` instruction.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, rdi
        ///     mov     rcx, rdx
        ///     sar     rcx, 63
        ///     add     rax, rdx
        ///     adc     rcx, rsi
        ///     mov     rdx, rcx
        ///     ret
        /// ```
        ///
        /// This optimizes well, for example, on `x86_64`,
        /// for a 256-bit addition (1x u128, 1x i128 + 1x i64), it
        /// optimizes to 2 `add`, 4 `adc`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// wrapping_add:
        ///     mov     rax, qword ptr [rsp + 16]
        ///     mov     r9, rax
        ///     sar     r9, 63
        ///     add     rcx, r9
        ///     adc     r9, r8
        ///     add     rsi, qword ptr [rsp + 8]
        ///     adc     rdx, rax
        ///     adc     rcx, 0
        ///     mov     rax, rdi
        ///     adc     r9, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r9
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_iwide(x0: $u, x1: $s, y: $s) -> ($u, $s) {
            let hi = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let (y0, y1) = (y as $u, hi as $s);
            $wrapping_full(x0, x1, y0, y1)
        }

        /// Const implementation to add a small, signed number to the wider type.
        ///
        /// Returns the value and if the add overflowed. This is effectively the
        /// implementation of the wider type, just with an extra bitshift to expand
        /// the type to the wider width.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, signed value.
        ///
        /// # Assembly
        ///
        /// This optimizes well, for example, on `x86_64`, for a 128-bit addition
        /// (1x u64, 1x i64 + 1x i64), it optimizes to 2 `add`, 1 `adc`, 2 `set`,
        /// 1 `or`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     mov     rdi, rcx
        ///     sar     rdi, 63
        ///     add     rdi, rdx
        ///     seto    dl
        ///     add     rsi, rcx
        ///     adc     rdi, 0
        ///     seto    cl
        ///     or      cl, dl
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdi
        ///     mov     byte ptr [rax + 16], cl
        ///     ret
        /// ```
        ///
        /// This optimizes well, for example, on `x86_64`, for a 256-bit addition
        /// (1x u128, 1x i128 + 1x i128), it optimizes to 2 `add`, 4 `adc`, 2 `set`,
        /// 1 `or`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// overflowing_add:
        ///     mov     rax, rdi
        ///     mov     rdi, qword ptr [rsp + 16]
        ///     mov     r9, rdi
        ///     sar     r9, 63
        ///     add     rcx, r9
        ///     adc     r9, r8
        ///     seto    r8b
        ///     add     rsi, qword ptr [rsp + 8]
        ///     adc     rdx, rdi
        ///     adc     rcx, 0
        ///     adc     r9, 0
        ///     seto    dil
        ///     or      dil, r8b
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], r9
        ///     mov     byte ptr [rax + 32], dil
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_iwide(x0: $u, x1: $s, y: $s) -> ($u, $s, bool) {
            let hi = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let (y0, y1) = (y as $u, hi as $s);
            $overflowing_full(x0, x1, y0, y1)
        }
    };
}

add_signed_impl!(
    u8,
    i8,
    wrapping_full => wrapping_add_i8,
    overflowing_full => overflowing_add_i8,
    wrapping_uwide => wrapping_add_uwide_i8,
    overflowing_uwide => overflowing_add_uwide_i8,
    wrapping_iwide => wrapping_add_iwide_i8,
    overflowing_iwide => overflowing_add_iwide_i8
);
add_signed_impl!(
    u16,
    i16,
    wrapping_full => wrapping_add_i16,
    overflowing_full => overflowing_add_i16,
    wrapping_uwide => wrapping_add_uwide_i16,
    overflowing_uwide => overflowing_add_uwide_i16,
    wrapping_iwide => wrapping_add_iwide_i16,
    overflowing_iwide => overflowing_add_iwide_i16
);
add_signed_impl!(
    u32,
    i32,
    wrapping_full => wrapping_add_i32,
    overflowing_full => overflowing_add_i32,
    wrapping_uwide => wrapping_add_uwide_i32,
    overflowing_uwide => overflowing_add_uwide_i32,
    wrapping_iwide => wrapping_add_iwide_i32,
    overflowing_iwide => overflowing_add_iwide_i32
);
add_signed_impl!(
    u64,
    i64,
    wrapping_full => wrapping_add_i64,
    overflowing_full => overflowing_add_i64,
    wrapping_uwide => wrapping_add_uwide_i64,
    overflowing_uwide => overflowing_add_uwide_i64,
    wrapping_iwide => wrapping_add_iwide_i64,
    overflowing_iwide => overflowing_add_iwide_i64
);
add_signed_impl!(
    u128,
    i128,
    wrapping_full => wrapping_add_i128,
    overflowing_full => overflowing_add_i128,
    wrapping_uwide => wrapping_add_uwide_i128,
    overflowing_uwide => overflowing_add_uwide_i128,
    wrapping_iwide => wrapping_add_iwide_i128,
    overflowing_iwide => overflowing_add_iwide_i128
);

macro_rules! sub_signed_impl {
    (
        $u:ty,
        $s:ty,wrapping_full =>
        $wrapping_full:ident,overflowing_full =>
        $overflowing_full:ident,wrapping_uwide =>
        $wrapping_uwide:ident,overflowing_uwide =>
        $overflowing_uwide:ident,wrapping_iwide =>
        $wrapping_iwide:ident,overflowing_iwide =>
        $overflowing_iwide:ident $(,)?
    ) => {
        /// Const implementation of `wrapping_sub` for internal algorithm use.
        ///
        /// Returns the value and if the sub underflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on `x86_64`, for a
        /// 128-bit subtraction (1x u64, 1x i64 + 1x u64), it optimizes
        /// to 1 `sub`, and 1 `sbb` instruction.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, rdi
        ///     sub     rax, rdx
        ///     sbb     rsi, rcx
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes very well, for example, on `x86_64`,
        /// for a 256-bit subtraction (1x u128, 1x i128 + x u64), it
        /// optimizes to 2 `sub` and 4 `sbb` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     sub     rcx, qword ptr [rsp + 24]
        ///     sbb     r8, qword ptr [rsp + 32]
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     mov     rax, rdi
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_full(x0: $u, x1: $s, y0: $u, y1: $s) -> ($u, $s) {
            // NOTE: When we ignore the carry in the caller, this optimizes the same.
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let (v0, c0) = x0.overflowing_sub(y0);
            let v1 = x1.wrapping_sub(y1);
            let v1 = v1.wrapping_sub(c0 as $s);
            (v0, v1)
        }

        /// Const implementation of `overflowing_sub` for internal algorithm use.
        ///
        /// Returns the value and if the sub underflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// This optimizes extremely well, for example, on `x86_64`,
        /// for a 128-bit subtraction (1x u64, 1x i64 + 1x u64, 1x u64),
        /// it optimizes to 2
        /// `sub`, 1 `sbb`, 2 `set`, and 1 `or` instruction.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     sub     rdx, r8
        ///     seto    dil
        ///     sub     rsi, rcx
        ///     sbb     rdx, 0
        ///     seto    cl
        ///     or      cl, dil
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     byte ptr [rax + 16], cl
        ///     ret
        /// ```
        ///
        /// This optimizes extremely well, for example, on `x86_64`, for
        /// a 256-bit subtraction (2x u128 + 2x u128), it optimizes to 2
        /// `sub`, 4 `sbb`, 2 `set` and 1 `or` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     sub     rcx, qword ptr [rsp + 24]
        ///     sbb     r8, qword ptr [rsp + 32]
        ///     seto    r9b
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     sbb     r8, 0
        ///     seto    dil
        ///     or      dil, r9b
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], r8
        ///     mov     byte ptr [rax + 32], dil
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_full(x0: $u, x1: $s, y0: $u, y1: $s) -> ($u, $s, bool) {
            // NOTE: When we ignore the carry in the caller, this optimizes the same.
            debug_assert!(<$u>::BITS == <$s>::BITS);
            let (v0, c0) = x0.overflowing_sub(y0);
            // FIXME: Move to `borrowing_sub` once stable.
            let (v1, c1) = x1.overflowing_sub(y1);
            let (v1, c2) = v1.overflowing_sub(c0 as $s);

            (v0, v1, c1 | c2)
        }

        /// Const implementation to subtract a small, unsigned number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, unsigned value.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on `x86_64`, for a
        /// 128-bit subtraction (1x u64, 1x i64 + 1x u64), it optimizes
        /// to 1 `sub`, and 1 `sbb` instruction.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, rdi
        ///     sub     rax, rdx
        ///     sbb     rsi, 0
        ///     mov     rdx, rsi
        ///     ret
        /// ```
        ///
        /// This optimizes fairly well, for example, on `x86_64`,
        /// for a 256-bit subtraction (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `sub` and 3 `sbb` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     mov     rax, rdi
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_uwide(x0: $u, x1: $s, y: $u) -> ($u, $s) {
            let (v0, c0) = x0.overflowing_sub(y);
            let v1 = x1.wrapping_sub(c0 as $s);
            (v0, v1)
        }

        /// Const implementation to subtract a small, unsigned number to the wider type.
        ///
        /// Returns the value and if the subtract overflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, unsigned value.
        ///
        /// # Assembly
        ///
        /// This optimizes very well, for example, on `x86_64`, for a
        /// 128-bit subtraction (1x u64, 1x i64 + 1x u64), it optimizes
        /// to 1 `sub`, 1 `sbb`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     sub     rsi, rcx
        ///     sbb     rdx, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     seto    byte ptr [rdi + 16]
        ///     ret
        /// ```
        ///
        /// This optimizes fairly well, for example, on `x86_64`,
        /// for a 256-bit subtraction (1x u128, 1x i128 + x u64), it
        /// optimizes to 1 `sub`, 3 `sbb`, and 1 `set` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     mov     rax, rdi
        ///     sbb     rdx, qword ptr [rsp + 16]
        ///     sbb     rcx, 0
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], rcx
        ///     mov     qword ptr [rdi + 24], r8
        ///     seto    byte ptr [rdi + 32]
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_uwide(x0: $u, x1: $s, y: $u) -> ($u, $s, bool) {
            let (v0, c0) = x0.overflowing_sub(y);
            let (v1, c1) = x1.overflowing_sub(c0 as $s);
            (v0, v1, c1)
        }

        /// Const implementation to subtract a small, unsigned number to the wider type.
        ///
        /// Returns the value, wrapping on overflow.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, unsigned value.
        ///
        /// # Assembly
        ///
        /// This optimizes well, for example, on `x86_64`,
        /// for a 128-bit subtraction (1x u64, 1x i64 + 1x i64), it
        /// optimizes to 1 `add`, 1 `sub`, 1 `sbb`, and 1 `shr`
        /// instruction.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, rdi
        ///     mov     rcx, rdx
        ///     shr     rcx, 63
        ///     add     rcx, rsi
        ///     sub     rax, rdx
        ///     sbb     rcx, 0
        ///     mov     rdx, rcx
        ///     ret
        /// ```
        ///
        /// This optimizes well, for example, on `x86_64`,
        /// for a 256-bit subtraction (1x u128, 1x i128 + 1x i64), it
        /// optimizes to 1 `add`, 1 `adc`, 1 `sub`, 3 `sbb`, and 1
        /// `shr` instructions.
        ///
        /// ```asm
        /// wrapping_sub:
        ///     mov     rax, qword ptr [rsp + 16]
        ///     mov     r9, rax
        ///     shr     r9, 63
        ///     add     r9, rcx
        ///     adc     r8, 0
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     sbb     rdx, rax
        ///     sbb     r9, 0
        ///     mov     rax, rdi
        ///     sbb     r8, 0
        ///     mov     qword ptr [rdi], rsi
        ///     mov     qword ptr [rdi + 8], rdx
        ///     mov     qword ptr [rdi + 16], r9
        ///     mov     qword ptr [rdi + 24], r8
        ///     ret
        /// ```
        #[inline]
        pub const fn $wrapping_iwide(x0: $u, x1: $s, y: $s) -> ($u, $s) {
            let hi = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let (y0, y1) = (y as $u, hi as $s);
            $wrapping_full(x0, x1, y0, y1)
        }

        /// Const implementation to subtract a small, signed number to the wider type.
        ///
        /// Returns the value and if the subtract overflowed.
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - The small, signed value.
        ///
        /// # Assembly
        ///
        /// This optimizes well, for example, on `x86_64`, for a 128-bit subtraction
        /// (1x u64, 1x i64 + 1x i64), it optimizes to 2 `sub`, 1 `sbb`, 2 `set`,
        /// 1 `or`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     mov     rdi, rcx
        ///     sar     rdi, 63
        ///     sub     rdx, rdi
        ///     seto    dil
        ///     sub     rsi, rcx
        ///     sbb     rdx, 0
        ///     seto    cl
        ///     or      cl, dil
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     byte ptr [rax + 16], cl
        ///     ret
        /// ```
        ///
        /// This optimizes well, for example, on `x86_64`, for a 256-bit subtraction
        /// (1x u128, 1x i128 + 1x i128), it optimizes to 2 `sub`, 4 `sbb`, 2 `set`,
        /// 1 `or`, and 1 `sar` instructions.
        ///
        /// ```asm
        /// overflowing_sub:
        ///     mov     rax, rdi
        ///     mov     rdi, qword ptr [rsp + 16]
        ///     mov     r9, rdi
        ///     sar     r9, 63
        ///     sub     rcx, r9
        ///     sbb     r8, r9
        ///     seto    r9b
        ///     sub     rsi, qword ptr [rsp + 8]
        ///     sbb     rdx, rdi
        ///     sbb     rcx, 0
        ///     sbb     r8, 0
        ///     seto    dil
        ///     or      dil, r9b
        ///     mov     qword ptr [rax], rsi
        ///     mov     qword ptr [rax + 8], rdx
        ///     mov     qword ptr [rax + 16], rcx
        ///     mov     qword ptr [rax + 24], r8
        ///     mov     byte ptr [rax + 32], dil
        ///     ret
        /// ```
        #[inline]
        pub const fn $overflowing_iwide(x0: $u, x1: $s, y: $s) -> ($u, $s, bool) {
            let hi = <$u>::MIN.wrapping_sub(y.is_negative() as $u);
            let (y0, y1) = (y as $u, hi as $s);
            $overflowing_full(x0, x1, y0, y1)
        }
    };
}

sub_signed_impl!(
    u8,
    i8,
    wrapping_full => wrapping_sub_i8,
    overflowing_full => overflowing_sub_i8,
    wrapping_uwide => wrapping_sub_uwide_i8,
    overflowing_uwide => overflowing_sub_uwide_i8,
    wrapping_iwide => wrapping_sub_iwide_i8,
    overflowing_iwide => overflowing_sub_iwide_i8
);
sub_signed_impl!(
    u16,
    i16,
    wrapping_full => wrapping_sub_i16,
    overflowing_full => overflowing_sub_i16,
    wrapping_uwide => wrapping_sub_uwide_i16,
    overflowing_uwide => overflowing_sub_uwide_i16,
    wrapping_iwide => wrapping_sub_iwide_i16,
    overflowing_iwide => overflowing_sub_iwide_i16
);
sub_signed_impl!(
    u32,
    i32,
    wrapping_full => wrapping_sub_i32,
    overflowing_full => overflowing_sub_i32,
    wrapping_uwide => wrapping_sub_uwide_i32,
    overflowing_uwide => overflowing_sub_uwide_i32,
    wrapping_iwide => wrapping_sub_iwide_i32,
    overflowing_iwide => overflowing_sub_iwide_i32
);
sub_signed_impl!(
    u64,
    i64,
    wrapping_full => wrapping_sub_i64,
    overflowing_full => overflowing_sub_i64,
    wrapping_uwide => wrapping_sub_uwide_i64,
    overflowing_uwide => overflowing_sub_uwide_i64,
    wrapping_iwide => wrapping_sub_iwide_i64,
    overflowing_iwide => overflowing_sub_iwide_i64
);
sub_signed_impl!(
    u128,
    i128,
    wrapping_full => wrapping_sub_i128,
    overflowing_full => overflowing_sub_i128,
    wrapping_uwide => wrapping_sub_uwide_i128,
    overflowing_uwide => overflowing_sub_uwide_i128,
    wrapping_iwide => wrapping_sub_iwide_i128,
    overflowing_iwide => overflowing_sub_iwide_i128
);

macro_rules! mul_signed_impl {
    // wrapping to signed
    (@wsign, $lo:expr, $hi:expr, $x:ident, $y:expr, $s:ty, $neg:ident) => {{
        // now convert to the right sign
        let hi = $hi as $s;
        let should_be_negative = ($x < 0) ^ ($y < 0);
        if !should_be_negative {
            ($lo, hi)
        } else {
            $neg($lo, hi)
        }
    }};

    // overflowing to signed
    (@osign, $lo:expr, $hi:expr, $over:expr, $x:ident, $y:expr, $s:ty, $neg:ident) => {{
        // now convert to the right sign
        let hi = $hi as $s;
        let is_negative = hi < 0;
        let should_be_negative = ($x < 0) ^ ($y < 0);
        if !should_be_negative {
            ($lo, hi, $over | is_negative)
        } else {
            // convert our unsigned integer to 2's complement from an
            // abs value. if our value is exactly `::MIN`, then it didn't
            // wrap and it shouldn't be negative
            // NOTE: We want to negate this, which will always work since
            // `::MAX + 1` will wrap to min as expected.
            let is_min = hi == <$s>::MIN;
            let (lo, hi) = $neg($lo, hi);
            (lo, hi, $over | (is_negative ^ is_min))
        }
    }};

    // split into 4 limbs, as an abs
    (@split4 $u:ty, $h:ty, $x:expr, $y:expr, $abs:ident) => {{
        let (xa, ya) = $abs($x, $y);
        split!($u, $h, xa, ya)
    }};

    // split into 2 limbs, as an abs
    (@split2 $u:ty, $h:ty, $x:expr) => {{
        let xa = $x.unsigned_abs();
        split!($u, $h, xa)
    }};

    (
        u => $u:ty,
        s => $s:ty,
        uh => $uh:ty,
        sh => $sh:ty,
        abs => $abs:ident,
        neg => $neg:ident,
        wrapping_array => $wrapping_array:ident,
        wrapping_full => $wrapping_full:ident,
        wrapping_uwide => $wrapping_uwide:ident,
        wrapping_iwide => $wrapping_iwide:ident,
        wrapping_ulimb => $wrapping_ulimb:ident,
        wrapping_ilimb => $wrapping_ilimb:ident,
        overflowing_array => $overflowing_array:ident,
        overflowing_full => $overflowing_full:ident,
        overflowing_uwide => $overflowing_uwide:ident,
        overflowing_iwide => $overflowing_iwide:ident,
        overflowing_ulimb => $overflowing_ulimb:ident,
        overflowing_ilimb => $overflowing_ilimb:ident,
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
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
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
        pub const fn $wrapping_full(x0: $u, x1: $s, y0: $u, y1: $s) -> ($u, $s) {
            let x = mul_signed_impl!(@split4 $u, $uh, x0, x1, $abs);
            let y = mul_signed_impl!(@split4 $u, $uh, y0, y1, $abs);
            let r = $wrapping_array(&x, &y);
            let (lo, hi) = unsplit!(@wrapping $u, r, <$uh>::BITS);
            mul_signed_impl!(@wsign, lo, hi, x1, y1, $s, $neg)
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
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - A small, unsigned factor to multiply by.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`u32`) which can add optimizations
        /// for scalar word processing.
        ///
        /// # Assembly
        ///
        /// For 256-bit multiplication, the results are fairly similar to the unsigned
        /// variant for algorithm (3), escape instead of having up to 8 `mul` and 12
        /// `add` instructions, it can have up to 8 `mul` and 15 `add` instructions.
        /// All the other optimization caveats are as described above.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $wrapping_uwide(x0: $u, x1: $s, y: $u) -> ($u, $s) {
            let x = mul_signed_impl!(@split4 $u, $uh, x0, x1, $abs);
            let y = split!($u, $uh, y);
            let r = $wrapping_array(&x, &y);
            let (lo, hi) = unsplit!(@wrapping $u, r, <$uh>::BITS);
            mul_signed_impl!(@wsign, lo, hi, x1, 0i32, $s, $neg)
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
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - A small, unsigned factor to multiply by.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`i32`) which can add optimizations
        /// for scalar word processing.
        ///
        /// # Assembly
        ///
        /// For 256-bit multiplication, the results are fairly similar to the unsigned
        /// variant for algorithm (3), escape instead of having up to 8 `mul` and 12
        /// `add` instructions, it can have up to 8 `mul` and 15 `add` instructions.
        /// All the other optimization caveats are as described above.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $wrapping_iwide(x0: $u, x1: $s, y: $s) -> ($u, $s) {
            let lhs = mul_signed_impl!(@split4 $u, $uh, x0, x1, $abs);
            let rhs = mul_signed_impl!(@split2 $u, $uh, y);
            let r = $wrapping_array(&lhs, &rhs);
            let (lo, hi) = unsplit!(@wrapping $u, r, <$uh>::BITS);
            mul_signed_impl!(@wsign, lo, hi, x1, y, $s, $neg)
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
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - A small, unsigned factor to multiply by.
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
        #[inline]
        pub const fn $wrapping_ulimb(x0: $u, x1: $s, y: $uh) -> ($u, $s) {
            let lhs = mul_signed_impl!(@split4 $u, $uh, x0, x1, $abs);
            let r = $wrapping_array(&lhs, &[y]);
            let (lo, hi) = unsplit!(@wrapping $u, r, <$uh>::BITS);
            mul_signed_impl!(@wsign, lo, hi, x1, 0i32, $s, $neg)
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
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - A small, unsigned factor to multiply by.
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
        #[inline]
        pub const fn $wrapping_ilimb(x0: $u, x1: $s, y: $sh) -> ($u, $s) {
            let lhs = mul_signed_impl!(@split4 $u, $uh, x0, x1, $abs);
            let r = $wrapping_array(&lhs, &[y.unsigned_abs()]);
            let (lo, hi) = unsplit!(@wrapping $u, r, <$uh>::BITS);
            mul_signed_impl!(@wsign, lo, hi, x1, y, $s, $neg)
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
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y0` - The lower half of y.
        /// * `y1` - The upper half of y.
        ///
        /// # Assembly
        ///
        /// The analysis here is practically identical to that of `wrapping_full`.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $overflowing_full(x0: $u, x1: $s, y0: $u, y1: $s) -> ($u, $s, bool) {
            let x = mul_signed_impl!(@split4 $u, $uh, x0, x1, $abs);
            let y = mul_signed_impl!(@split4 $u, $uh, y0, y1, $abs);
            let r = $overflowing_array(&x, &y);
            let (lo, hi, overflowed) = unsplit!(@overflow $u, r, <$uh>::BITS);
            mul_signed_impl!(@osign, lo, hi, overflowed, x1, y1, $s, $neg)
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
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - A small, unsigned factor to multiply by.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`u32`) which can add optimizations
        /// for scalar word processing.
        ///
        /// # Assembly
        ///
        /// The analysis here is practically identical to that of `wrapping_uwide`.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $overflowing_uwide(x0: $u, x1: $s, y: $u) -> ($u, $s, bool) {
            let x = mul_signed_impl!(@split4 $u, $uh, x0, x1, $abs);
            let y = split!($u, $uh, y);
            let r = $overflowing_array(&x, &y);
            let (lo, hi, overflowed) = unsplit!(@overflow $u, r, <$uh>::BITS);
            mul_signed_impl!(@osign, lo, hi, overflowed, x1, 0i32, $s, $neg)
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
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - A small, unsigned factor to multiply by.
        ///
        /// This multiplies a wide value, say, an `i64` as `(u32, i32)`
        /// pairs by a small value (`i32`) which can add optimizations
        /// for scalar word processing.
        ///
        /// # Assembly
        ///
        /// The analysis here is practically identical to that of `wrapping_iwide`.
        ///
        /// [`mulx`]: https://www.felixcloutier.com/x86/mulx
        #[inline]
        pub const fn $overflowing_iwide(x0: $u, x1: $s, y: $s) -> ($u, $s, bool) {
            let lhs = mul_signed_impl!(@split4 $u, $uh, x0, x1, $abs);
            let rhs = mul_signed_impl!(@split2 $u, $uh, y);
            let r = $overflowing_array(&lhs, &rhs);
            let (lo, hi, overflowed) = unsplit!(@overflow $u, r, <$uh>::BITS);
            mul_signed_impl!(@osign, lo, hi, overflowed, x1, y, $s, $neg)
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
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - A small, unsigned factor to multiply by.
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
        #[inline]
        pub const fn $overflowing_ulimb(x0: $u, x1: $s, y: $uh) -> ($u, $s, bool) {
            let lhs = mul_signed_impl!(@split4 $u, $uh, x0, x1, $abs);
            let r = $overflowing_array(&lhs, &[y]);
            let (lo, hi, overflowed) = unsplit!(@overflow $u, r, <$uh>::BITS);
            mul_signed_impl!(@osign, lo, hi, overflowed, x1, 0i32, $s, $neg)
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
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `y` - A small, unsigned factor to multiply by.
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
        #[inline]
        pub const fn $overflowing_ilimb(x0: $u, x1: $s, y: $sh) -> ($u, $s, bool) {
            let lhs = mul_signed_impl!(@split4 $u, $uh, x0, x1, $abs);
            let r = $overflowing_array(&lhs, &[y.unsigned_abs()]);
            let (lo, hi, overflowed) = unsplit!(@overflow $u, r, <$uh>::BITS);
            mul_signed_impl!(@osign, lo, hi, overflowed, x1, y, $s, $neg)
        }
    };
}

mul_signed_impl!(
    u => u16,
    s => i16,
    uh => u8,
    sh => i8,
    abs => unsigned_abs_i16,
    neg => neg_i16,
    wrapping_array => wrapping_mul_arr_u16,
    wrapping_full => wrapping_mul_i16,
    wrapping_uwide => wrapping_mul_uwide_i16,
    wrapping_iwide => wrapping_mul_iwide_i16,
    wrapping_ulimb => wrapping_mul_ulimb_i16,
    wrapping_ilimb => wrapping_mul_ilimb_i16,
    overflowing_array => overflowing_mul_arr_u16,
    overflowing_full => overflowing_mul_i16,
    overflowing_uwide => overflowing_mul_uwide_i16,
    overflowing_iwide => overflowing_mul_iwide_i16,
    overflowing_ulimb => overflowing_mul_ulimb_i16,
    overflowing_ilimb => overflowing_mul_ilimb_i16,
);
mul_signed_impl!(
    u => u32,
    s => i32,
    uh => u16,
    sh => i16,
    abs => unsigned_abs_i32,
    neg => neg_i32,
    wrapping_array => wrapping_mul_arr_u32,
    wrapping_full => wrapping_mul_i32,
    wrapping_uwide => wrapping_mul_uwide_i32,
    wrapping_iwide => wrapping_mul_iwide_i32,
    wrapping_ulimb => wrapping_mul_ulimb_i32,
    wrapping_ilimb => wrapping_mul_ilimb_i32,
    overflowing_array => overflowing_mul_arr_u32,
    overflowing_full => overflowing_mul_i32,
    overflowing_uwide => overflowing_mul_uwide_i32,
    overflowing_iwide => overflowing_mul_iwide_i32,
    overflowing_ulimb => overflowing_mul_ulimb_i32,
    overflowing_ilimb => overflowing_mul_ilimb_i32,
);
mul_signed_impl!(
    u => u64,
    s => i64,
    uh => u32,
    sh => i32,
    abs => unsigned_abs_i64,
    neg => neg_i64,
    wrapping_array => wrapping_mul_arr_u64,
    wrapping_full => wrapping_mul_i64,
    wrapping_uwide => wrapping_mul_uwide_i64,
    wrapping_iwide => wrapping_mul_iwide_i64,
    wrapping_ulimb => wrapping_mul_ulimb_i64,
    wrapping_ilimb => wrapping_mul_ilimb_i64,
    overflowing_array => overflowing_mul_arr_u64,
    overflowing_full => overflowing_mul_i64,
    overflowing_uwide => overflowing_mul_uwide_i64,
    overflowing_iwide => overflowing_mul_iwide_i64,
    overflowing_ulimb => overflowing_mul_ulimb_i64,
    overflowing_ilimb => overflowing_mul_ilimb_i64,
);
mul_signed_impl!(
    u => u128,
    s => i128,
    uh => u64,
    sh => i64,
    abs => unsigned_abs_i128,
    neg => neg_i128,
    wrapping_array => wrapping_mul_arr_u128,
    wrapping_full => wrapping_mul_i128,
    wrapping_uwide => wrapping_mul_uwide_i128,
    wrapping_iwide => wrapping_mul_iwide_i128,
    wrapping_ulimb => wrapping_mul_ulimb_i128,
    wrapping_ilimb => wrapping_mul_ilimb_i128,
    overflowing_array => overflowing_mul_arr_u128,
    overflowing_full => overflowing_mul_i128,
    overflowing_uwide => overflowing_mul_uwide_i128,
    overflowing_iwide => overflowing_mul_iwide_i128,
    overflowing_ulimb => overflowing_mul_ulimb_i128,
    overflowing_ilimb => overflowing_mul_ilimb_i128,
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
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `shift` - The number of bits to shift.
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
        /// On x86, this is done via the `sar` instruction, which is
        ///
        /// * `x0` - The lower half of x.
        /// * `x1` - The upper half of x.
        /// * `shift` - The number of bits to shift.
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
    u8, i8 => shl_i8, shr_i8,
    u16, i16 => shl_i16, shr_i16,
    u32, i32 => shl_i32, shr_i32,
    u64, i64 => shl_i64, shr_i64,
    u128, i128 => shl_i128, shr_i128,
}

// UNARY OPS - SIGNED
// ------------------

macro_rules! swap_signed_impl {
    ($($u:ty, $s:ty => $swap_bytes:ident, $reverse_bits:ident,)*) => ($(
        /// Reverses the byte order of the integer.
        ///
        /// # Assembly
        ///
        /// This optimizes very nicely, with efficient `bswap` or `rol`
        /// implementations for each.
        #[inline]
        pub const fn $swap_bytes(x0: $u, x1: $s) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            (x1.swap_bytes() as $u, x0.swap_bytes() as $s)
        }

        /// Reverses the order of bits in the integer.
        ///
        /// The least significant bit becomes the most significant bit, second
        /// least-significant bit becomes second most-significant bit, etc.
        /// Reversing bits is also quite inefficient, and for 128-bit and
        /// larger integers (2x `u64`), this is just as efficient as the
        /// native implementation. For smaller type sizes, the compiler can
        /// optimize the implementation, but we go beyond that realm.
        #[inline]
        pub const fn $reverse_bits(x0: $u, x1: $s) -> ($u, $s) {
            debug_assert!(<$u>::BITS == <$s>::BITS);
            // NOTE: Reversing bits is identical to unsigned.
            ((x1 as $u).reverse_bits(), x0.reverse_bits() as $s)
        }
    )*);
}

swap_signed_impl! {
    u8, i8 =>swap_bytesi8, reverse_bits_i8,
    u16, i16 => swap_bytes_i16, reverse_bits_i16,
    u32, i32 => swap_bytes_i32, reverse_bits_i32,
    u64, i64 => swap_bytes_i64, reverse_bits_i64,
    u128, i128 => swap_bytes_i128, reverse_bits_i128,
}

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
    u8, i8 => rotate_left_i8, rotate_right_i8,
    u16, i16 => rotate_left_i16, rotate_right_i16,
    u32, i32 => rotate_left_i32, rotate_right_i32,
    u64, i64 => rotate_left_i64, rotate_right_i64,
    u128, i128 => rotate_left_i128, rotate_right_i128,
}

macro_rules! not_impl {
    ($u:ty, $s:ty, $func:ident) => {
        /// Const implementation of `Not` for internal algorithm use.
        #[inline(always)]
        pub const fn $func(lo: $u, hi: $s) -> ($u, $s) {
            (!lo, !hi)
        }
    };
}

not_impl!(u8, i8, not_i8);
not_impl!(u16, i16, not_i16);
not_impl!(u32, i32, not_i32);
not_impl!(u64, i64, not_i64);
not_impl!(u128, i128, not_i128);

macro_rules! neg_impl {
    ($u:ty, $s:ty, $func:ident) => {
        /// Const implementation of `Neg` for internal algorithm use.
        #[inline(always)]
        pub const fn $func(lo: $u, hi: $s) -> ($u, $s) {
            // NOTE: This is identical to `add(not(x), 1i256)`
            // This assumes two's complement
            let (lo, hi) = (!lo, !hi);
            let (lo, c) = lo.overflowing_add(1);
            let hi = hi.wrapping_add(c as $s);
            (lo, hi)
        }
    };
}

neg_impl!(u8, i8, neg_i8);
neg_impl!(u16, i16, neg_i16);
neg_impl!(u32, i32, neg_i32);
neg_impl!(u64, i64, neg_i64);
neg_impl!(u128, i128, neg_i128);

macro_rules! wrapping_abs_impl {
    ($u:ty, $s:ty, $func:ident, $neg:ident) => {
        /// Wrapping (modular) absolute value. Computes `self.abs()`, wrapping
        /// around at the boundary of the type.
        #[inline(always)]
        pub const fn $func(lo: $u, hi: $s) -> ($u, $s) {
            if hi < 0 {
                $neg(lo, hi)
            } else {
                (lo, hi)
            }
        }
    };
}

wrapping_abs_impl!(u8, i8, wrapping_abs_i8, neg_i8);
wrapping_abs_impl!(u16, i16, wrapping_abs_i16, neg_i16);
wrapping_abs_impl!(u32, i32, wrapping_abs_i32, neg_i32);
wrapping_abs_impl!(u64, i64, wrapping_abs_i64, neg_i64);
wrapping_abs_impl!(u128, i128, wrapping_abs_i128, neg_i128);

macro_rules! unsigned_abs_impl {
    ($u:ty, $s:ty, $func:ident, $wrapping:ident) => {
        /// unsigned (modular) absolute value. Computes `self.abs()`, unsigned
        /// around at the boundary of the type.
        #[inline(always)]
        pub const fn $func(lo: $u, hi: $s) -> ($u, $u) {
            let (lo, hi) = $wrapping(lo, hi);
            (lo, hi as $u)
        }
    };
}

unsigned_abs_impl!(u8, i8, unsigned_abs_i8, wrapping_abs_i8);
unsigned_abs_impl!(u16, i16, unsigned_abs_i16, wrapping_abs_i16);
unsigned_abs_impl!(u32, i32, unsigned_abs_i32, wrapping_abs_i32);
unsigned_abs_impl!(u64, i64, unsigned_abs_i64, wrapping_abs_i64);
unsigned_abs_impl!(u128, i128, unsigned_abs_i128, wrapping_abs_i128);

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
    u8,
    i8,
    as_uwide => as_uwide_i8,
    as_unarrow => as_unarrow_i8,
    as_iwide => as_iwide_i8,
    as_inarrow => as_inarrow_i8,
    wide_cast => wide_cast_i8
);
signed_primitive_cast!(
    u16,
    i16,
    as_uwide => as_uwide_i16,
    as_unarrow => as_unarrow_i16,
    as_iwide => as_iwide_i16,
    as_inarrow => as_inarrow_i16,
    wide_cast => wide_cast_i16
);
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
        assert_eq!(overflowing_add_u32(1, 0, 1, 0), (2, 0, false));
        assert_eq!(overflowing_add_u32(u32::MAX, 0, u32::MAX, 0), (u32::MAX - 1, 1, false));
        assert_eq!(overflowing_add_u32(u32::MAX, 1, u32::MAX, 0), (u32::MAX - 1, 2, false));
        assert_eq!(overflowing_add_u32(u32::MAX, u32::MAX, 1, 0), (0, 0, true));
        assert_eq!(overflowing_add_u32(u32::MAX, u32::MAX, 2, 0), (1, 0, true));
        assert_eq!(
            overflowing_add_u32(u32::MAX, u32::MAX, u32::MAX, u32::MAX),
            (u32::MAX - 1, u32::MAX, true)
        );
    }

    #[test]
    fn overflowing_sub_u32_test() {
        assert_eq!(overflowing_sub_u32(0, 0, 1, 0), (u32::MAX, u32::MAX, true));
        assert_eq!(overflowing_sub_u32(1, 0, 1, 0), (0, 0, false));
        assert_eq!(overflowing_sub_u32(1, 0, 0, 0), (1, 0, false));
        assert_eq!(overflowing_sub_u32(u32::MAX, 1, 0, 2), (u32::MAX, u32::MAX, true));
        assert_eq!(overflowing_sub_u32(0, 1, 0, 2), (0, 4294967295, true));
        assert_eq!(overflowing_sub_u32(0, 1, 1, 1), (u32::MAX, u32::MAX, true));
    }

    #[test]
    fn overflowing_mul_u32_test() {
        assert_eq!(overflowing_mul_u32(u32::MAX, u32::MAX, u32::MAX, u32::MAX), (1, 0, true));
        assert_eq!(overflowing_mul_u32(1, 0, u32::MAX, 1), (u32::MAX, 1, false));
        assert_eq!(overflowing_mul_u32(2, 0, 2147483648, 0), (0, 1, false));
        assert_eq!(overflowing_mul_u32(1, 0, 1, 0), (1, 0, false));
        assert_eq!(overflowing_mul_u32(1, 0, 0, 0), (0, 0, false));
        assert_eq!(overflowing_mul_u32(u32::MAX, 1, 0, 2), (0, u32::MAX - 1, true));
        assert_eq!(overflowing_mul_u32(0, 1, 0, 2), (0, 0, true));
        // NOTE: This fails for small
        assert_eq!(overflowing_mul_u32(67, 0, 64103990, 0), (34, 1, false));
    }

    #[test]
    fn wrapping_mul_wide_u32_test() {
        assert_eq!(wrapping_mul_wide_u32(67, 0, 64103990), (34, 1));
        assert_eq!(wrapping_mul_wide_u32(2, 0, 2147483648), (0, 1));
        assert_eq!(wrapping_mul_wide_u32(0, 2147483648, 2), (0, 0));
        assert_eq!(wrapping_mul_wide_u32(2, 2147483648, 2), (4, 0));
        assert_eq!(wrapping_mul_wide_u32(2147483647, 2147483647, 2), (4294967294, 4294967294));
    }

    #[test]
    fn overflowing_mul_wide_u32_test() {
        assert_eq!(overflowing_mul_wide_u32(67, 0, 64103990), (34, 1, false));
        assert_eq!(overflowing_mul_wide_u32(2, 0, 2147483648), (0, 1, false));
        assert_eq!(overflowing_mul_wide_u32(0, 2147483648, 2), (0, 0, true));
        assert_eq!(overflowing_mul_wide_u32(2, 2147483648, 2), (4, 0, true));
        assert_eq!(
            overflowing_mul_wide_u32(2147483647, 2147483647, 2),
            (4294967294, 4294967294, false)
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
        assert_eq!(overflowing_add_i32(1, 0, 1, 0), (2, 0, false));
        assert_eq!(overflowing_add_i32(u32::MAX, 0, u32::MAX, 0), (u32::MAX - 1, 1, false));
        assert_eq!(overflowing_add_i32(u32::MAX, 1, u32::MAX, 0), (u32::MAX - 1, 2, false));
        assert_eq!(overflowing_add_i32(u32::MAX, i32::MAX, 1, 0), (0, i32::MIN, true));
        assert_eq!(overflowing_add_i32(u32::MAX, i32::MAX, 2, 0), (1, i32::MIN, true));
        assert_eq!(
            overflowing_add_i32(u32::MAX, i32::MAX, u32::MAX, i32::MAX),
            (u32::MAX - 1, -1, true)
        );
    }

    #[test]
    fn wrapping_mul_i32_test() {
        assert_eq!(wrapping_mul_i32(1, 0, 0, 1), (0, 1));
        assert_eq!(wrapping_mul_i32(u32::MAX, u32::MAX as i32, 1, 0), (u32::MAX, u32::MAX as i32));
    }

    #[test]
    fn overflowing_mul_i32_test() {
        // -1 * -2^31, which should wrap exactly
        assert_eq!(
            overflowing_mul_i32(u32::MAX, u32::MAX as i32, 0, i32::MIN),
            (0, i32::MIN, true)
        );
        assert_eq!(
            overflowing_mul_i32(u32::MAX, u32::MAX as i32, 0, i32::MAX),
            (0, -i32::MAX, false)
        );
        assert_eq!(
            overflowing_mul_i32(u32::MAX, u32::MAX as i32, 0, 0x80000000u32 as i32),
            (0, i32::MIN, true)
        );
        assert_eq!(overflowing_mul_i32(0, i32::MIN, 1, 0), (0, i32::MIN, false));
        assert_eq!(overflowing_mul_i32(u32::MAX, i32::MIN, 1, 0), (u32::MAX, i32::MIN, false));
        assert_eq!(overflowing_mul_i32(u32::MAX, i32::MIN, 0, 0), (0, 0, false));
    }
}
