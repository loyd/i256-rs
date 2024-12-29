//! Bitwise left and right shifts.

use crate::UWide;

macro_rules! define {
    (
        unsigned_type =>
        $u:ty,signed_type =>
        $s:ty,left =>
        $left:ident,right =>
        $right:ident,left_unsigned =>
        $left_unsigned:ident,right_unsigned =>
        $right_unsigned:ident,left_signed =>
        $left_signed:ident,right_signed =>
        $right_signed:ident $(,)?
    ) => {
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
        #[must_use]
        pub const fn $left<const N: usize, const SIGNED: bool>(x: [$u; N], shift: u32) -> [$u; N] {
            // NOTE: Signed and unsigned are identical
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
        #[must_use]
        pub const fn $right<const N: usize, const SIGNED: bool>(x: [$u; N], shift: u32) -> [$u; N] {
            assert!(N >= 2, "must have at least 2 limbs");
            const BITS: u32 = <$u>::BITS;
            debug_assert!(shift < N as u32 * BITS, "attempt to shift right with overflow");
            let limb_n = shift as usize >> BITS.trailing_zeros();
            let bits_n = shift & (BITS - 1);
            let inv_n = BITS - bits_n;

            // handlers for signed: signed rounds to -Inf
            let mut result = if SIGNED && (ne_index!(x[N - 1]) as $s) < 0 {
                [<$u>::MAX; N]
            } else {
                [0; N]
            };

            if N == 2 {
                // Simple case, only have to worry about swapping bits, no digits.
                let x0 = ne_index!(x[0]);
                let x1 = ne_index!(x[1]);
                let (r0, r1) = if limb_n != 0 {
                    if SIGNED {
                        let lo = (x1 as $s) >> bits_n;
                        let hi = ((x1 as $s) >> (BITS - 1));
                        (lo as $u, hi as $u)
                    } else {
                        (x1 >> bits_n, 0)
                    }
                } else if bits_n == 0 {
                    (x0, x1)
                } else {
                    // NOTE: We have `0xABCD_EFGH`, and we want to shift by 1,
                    // so to `0x0ABC_DEFG`, or we need to carry the `D`. So,
                    // our mask needs to be `0x000X`, or `0xXXXX >> (4 - 1)`,
                    // and then the value needs to be shifted left `<< (4 - 1)`.
                    let hi = if SIGNED {
                        ((x1 as $s) >> bits_n) as $u
                    } else {
                        x1 >> bits_n
                    };
                    let lo = x0 >> bits_n;
                    let carry = x1 << (inv_n);
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
                    // NOTE: remember this rounds to -Inf if signed, 0 otherwise
                    let ri = if SIGNED && index == N - 1 {
                        ((xi as $s) >> bits_n) as $u
                    } else {
                        xi >> bits_n
                    };

                    ne_index!(result[index - limb_n] = ri | carry);
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

        #[must_use]
        #[inline(always)]
        pub const fn $left_unsigned<const N: usize>(x: [$u; N], shift: u32) -> [$u; N] {
            $left::<N, false>(x, shift)
        }

        #[must_use]
        #[inline(always)]
        pub const fn $right_unsigned<const N: usize>(x: [$u; N], shift: u32) -> [$u; N] {
            $right::<N, false>(x, shift)
        }

        #[must_use]
        #[inline(always)]
        pub const fn $left_signed<const N: usize>(x: [$u; N], shift: u32) -> [$u; N] {
            $left::<N, true>(x, shift)
        }

        #[must_use]
        #[inline(always)]
        pub const fn $right_signed<const N: usize>(x: [$u; N], shift: u32) -> [$u; N] {
            $right::<N, true>(x, shift)
        }
    };
}

define!(
    unsigned_type => u32,
    signed_type => i32,
    left => left_32,
    right => right_32,
    left_unsigned => left_u32,
    right_unsigned => right_u32,
    left_signed => left_i32,
    right_signed => right_i32,
);
define!(
    unsigned_type => u64,
    signed_type => i64,
    left => left_64,
    right => right_64,
    left_unsigned => left_u64,
    right_unsigned => right_u64,
    left_signed => left_i64,
    right_signed => right_i64,
);
define!(
    unsigned_type => u128,
    signed_type => i128,
    left => left_128,
    right => right_128,
    left_unsigned => left_u128,
    right_unsigned => right_u128,
    left_signed => left_i128,
    right_signed => right_i128,
);

limb_function!(left_uwide, left_u128, left_u64, [UWide; N], u32, ret => [UWide; N]);
limb_function!(right_uwide, right_u128, right_u64, [UWide; N], u32, ret => [UWide; N]);
limb_function!(left_iwide, left_i128, left_i64, [UWide; N], u32, ret => [UWide; N]);
limb_function!(right_iwide, right_i128, right_i64, [UWide; N], u32, ret => [UWide; N]);

#[cfg(test)]
mod tests {
    use super::*;

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
        assert_eq!(from_le_shift([1, 0], 1, left_u32), [2, 0]);
        assert_eq!(from_le_shift([0, 1], 0, left_u32), [0, 1]);
        assert_eq!(from_le_shift([0, 1], 1, left_u32), [0, 2]);
        assert_eq!(from_le_shift([1, 0], 32, left_u32), [0, 1]);
        assert_eq!(from_le_shift([0, 1], 32, left_u32), [0, 0]);
        assert_eq!(from_le_shift([2, 0], 31, left_u32), [0, 1]);
        assert_eq!(from_le_shift([0, 2], 31, left_u32), [0, 0]);
        assert_eq!(from_le_shift([1, 2], 31, left_u32), [2147483648, 0]);

        // try some digit shifts as well
        assert_eq!(from_le_shift([1, 2, 3], 31, left_u32), [2147483648, 0, 2147483649]);
        assert_eq!(from_le_shift([1, 2, 0], 31, left_u32), [2147483648, 0, 1]);
        assert_eq!(from_le_shift([1, 2, 3], 32, left_u32), [0, 1, 2]);
        assert_eq!(from_le_shift([1, 2, 3], 63, left_u32), [0, 2147483648, 0]);
        assert_eq!(from_le_shift([1, 2, 3], 64, left_u32), [0, 0, 1]);
        assert_eq!(from_le_shift([1, 2, 3], 95, left_u32), [0, 0, 2147483648]);
        assert_eq!(from_le_shift([1, 2, 3], 0, left_u32), [1, 2, 3]);
    }

    #[test]
    fn shr_u32_test() {
        assert_eq!(from_le_shift([1, 0], 1, right_u32), [0, 0]);
        assert_eq!(from_le_shift([0, 1], 0, right_u32), [0, 1]);
        assert_eq!(from_le_shift([0, 1], 1, right_u32), [2147483648, 0]);
        assert_eq!(from_le_shift([1, 0], 32, right_u32), [0, 0]);
        assert_eq!(from_le_shift([0, 1], 32, right_u32), [1, 0]);
        assert_eq!(from_le_shift([2, 0], 31, right_u32), [0, 0]);
        assert_eq!(from_le_shift([0, 2], 31, right_u32), [4, 0]);
        assert_eq!(from_le_shift([1, 2], 31, right_u32), [4, 0]);

        // try some digit shifts as well
        assert_eq!(from_le_shift([1, 2, 3], 31, right_u32), [4, 6, 0]);
        assert_eq!(from_le_shift([1, 2, 0], 31, right_u32), [4, 0, 0]);
        assert_eq!(from_le_shift([1, 2, 3], 32, right_u32), [2, 3, 0]);
        assert_eq!(from_le_shift([1, 2, 3], 63, right_u32), [6, 0, 0]);
        assert_eq!(from_le_shift([1, 2, 3], 64, right_u32), [3, 0, 0]);
        assert_eq!(from_le_shift([1, 2, 3], 95, right_u32), [0, 0, 0]);
        assert_eq!(from_le_shift([1, 2, 3], 0, right_u32), [1, 2, 3]);
    }
}
