//! Left and right bitwise rotations (similar to `rol` and `ror`).

use crate::UWide;

macro_rules! define {
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
        #[must_use]
        #[inline(always)]
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
        #[must_use]
        #[inline(always)]
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

define! {
    u32 => left_u32, right_u32,
    u64 => left_u64, right_u64,
    u128 => left_u128, right_u128,
}

limb_function!(left_wide, left_u128, left_u64, [UWide; N], u32, ret => [UWide; N]);
limb_function!(right_wide, right_u128, right_u64, [UWide; N], u32, ret => [UWide; N]);
