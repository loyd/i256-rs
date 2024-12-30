//! Arithmetic utilities from small, native integer components.
//!
//! This allows the construction of larger type sizes from native,
//! fast integers.

#![doc(hidden)]

use crate::{ILimb, ULimb};

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

macro_rules! unsigned_define {
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

unsigned_define!(
    type => u32,
    wide => u64,
    wrapping_full => wrapping_u32,
    wrapping_limb => wrapping_limb_u32,
    overflowing_full => overflowing_u32,
    overflowing_limb => overflowing_limb_u32,
);
unsigned_define!(
    type => u64,
    wide => u128,
    wrapping_full => wrapping_u64,
    wrapping_limb => wrapping_limb_u64,
    overflowing_full => overflowing_u64,
    overflowing_limb => overflowing_limb_u64,
);

limb_function!(wrapping_unsigned, wrapping_u64, wrapping_u32, &[ULimb; N], ret => [ULimb; N]);
limb_function!(overflowing_unsigned, overflowing_u64, overflowing_u32, &[ULimb; N], &[ULimb; N], ret => ([ULimb; N], bool));

limb_function!(wrapping_limb, wrapping_limb_u64, wrapping_limb_u32, &[ULimb; N], ULimb, ret => [ULimb; N]);
limb_function!(overflowing_limb, overflowing_limb_u64, overflowing_limb_u32, &[ULimb; N], ULimb, ret => ([ULimb; N], bool));

macro_rules! signed_define {
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

signed_define!(
    unsigned => u32,
    signed => i32,
    wrapping_unsigned => wrapping_u32,
    wrapping_full => wrapping_i32,
    wrapping_ulimb => wrapping_ulimb_i32,
    wrapping_ilimb => wrapping_ilimb_i32,
    overflowing_unsigned => overflowing_u32,
    overflowing_full => overflowing_i32,
    overflowing_ulimb => overflowing_ulimb_i32,
    overflowing_ilimb => overflowing_ilimb_i32,
);
signed_define!(
    unsigned => u64,
    signed => i64,
    wrapping_unsigned => wrapping_u64,
    wrapping_full => wrapping_i64,
    wrapping_ulimb => wrapping_ulimb_i64,
    wrapping_ilimb => wrapping_ilimb_i64,
    overflowing_unsigned => overflowing_u64,
    overflowing_full => overflowing_i64,
    overflowing_ulimb => overflowing_ulimb_i64,
    overflowing_ilimb => overflowing_ilimb_i64,
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
    fn overflowing_mul_u32_test() {
        assert_eq!(
            from_le_over(&[u32::MAX, u32::MAX], &[u32::MAX, u32::MAX], overflowing_u32),
            ([1, 0], true)
        );
        assert_eq!(from_le_over(&[1, 0], &[u32::MAX, 1], overflowing_u32), ([u32::MAX, 1], false));
        assert_eq!(from_le_over(&[2, 0], &[2147483648, 0], overflowing_u32), ([0, 1], false));
        assert_eq!(from_le_over(&[1, 0], &[1, 0], overflowing_u32), ([1, 0], false));
        assert_eq!(from_le_over(&[1, 0], &[0, 0], overflowing_u32), ([0, 0], false));
        assert_eq!(
            from_le_over(&[u32::MAX, 1], &[0, 2], overflowing_u32),
            ([0, u32::MAX - 1], true)
        );
        assert_eq!(from_le_over(&[0, 1], &[0, 2], overflowing_u32), ([0, 0], true));
        // NOTE: This fails for small
        assert_eq!(from_le_over(&[67, 0], &[64103990, 0], overflowing_u32), ([34, 1], false));
    }

    #[test]
    fn wrapping_mul_limb_u32_test() {
        assert_eq!(from_le_limb_wrap(&[67, 0], 64103990, wrapping_limb_u32), [34, 1]);
        assert_eq!(from_le_limb_wrap(&[2, 0], 2147483648, wrapping_limb_u32), [0, 1]);
        assert_eq!(from_le_limb_wrap(&[0, 2147483648], 2, wrapping_limb_u32), [0, 0]);
        assert_eq!(from_le_limb_wrap(&[2, 2147483648], 2, wrapping_limb_u32), [4, 0]);
        assert_eq!(from_le_limb_wrap(&[2147483647, 2147483647], 2, wrapping_limb_u32), [
            4294967294, 4294967294
        ]);
    }

    #[test]
    fn overflowing_mul_limb_u32_test() {
        assert_eq!(from_le_limb_over(&[67, 0], 64103990, overflowing_limb_u32), ([34, 1], false));
        assert_eq!(from_le_limb_over(&[2, 0], 2147483648, overflowing_limb_u32), ([0, 1], false));
        assert_eq!(from_le_limb_over(&[0, 2147483648], 2, overflowing_limb_u32), ([0, 0], true));
        assert_eq!(from_le_limb_over(&[2, 2147483648], 2, overflowing_limb_u32), ([4, 0], true));
        assert_eq!(
            from_le_limb_over(&[2147483647, 2147483647], 2, overflowing_limb_u32),
            ([4294967294, 4294967294], false)
        );
    }

    #[test]
    fn wrapping_mul_i32_test() {
        assert_eq!(from_le_wrap(&[1, 0], &[0, 1], wrapping_i32), [0, 1]);
        assert_eq!(from_le_wrap(&[u32::MAX, u32::MAX], &[1, 0], wrapping_i32), [
            u32::MAX,
            u32::MAX
        ]);
    }

    #[test]
    fn overflowing_mul_i32_test() {
        // -1 * -2^31, which should wrap exactly
        assert_eq!(
            from_le_over(&[u32::MAX, u32::MAX], &[0, i32::MIN as u32], overflowing_i32),
            ([0, i32::MIN as u32], true)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, u32::MAX], &[0, i32::MAX as u32], overflowing_i32),
            ([0, -i32::MAX as u32], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, u32::MAX], &[0, 0x80000000u32], overflowing_i32),
            ([0, i32::MIN as u32], true)
        );
        assert_eq!(
            from_le_over(&[0, i32::MIN as u32], &[1, 0], overflowing_i32),
            ([0, i32::MIN as u32], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, i32::MIN as u32], &[1, 0], overflowing_i32),
            ([u32::MAX, i32::MIN as u32], false)
        );
        assert_eq!(
            from_le_over(&[u32::MAX, i32::MIN as u32], &[0, 0], overflowing_i32),
            ([0, 0], false)
        );
    }
}
