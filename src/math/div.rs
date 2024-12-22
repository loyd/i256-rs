// Licensed to the Apache Software Foundation (ASF) under one
// or more contributor license agreements.  See the NOTICE file
// distributed with this work for additional information
// regarding copyright ownership.  The ASF licenses this file
// to you under the Apache License, Version 2.0 (the
// "License"); you may not use this file except in compliance
// with the License.  You may obtain a copy of the License at
//
//   http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing,
// software distributed under the License is distributed on an
// "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
// KIND, either express or implied.  See the License for the
// specific language governing permissions and limitations
// under the License.

//! N-digit division
//!
//! Implementation heavily inspired by [uint]
//!
//! [uint]: https://github.com/paritytech/parity-common/blob/d3a9327124a66e52ca1114bb8640c02c18c134b8/uint/src/uint.rs#L844

use core::cmp::Ordering;

use super::types::{ULimb, UWide};

// NOTE: This cannot be made `const`, nor should it be attempted to be made so.
// We had a Knuth division algorithm previously in lexical, but it was removed
// for a few reasons, so we prioritize this. It used extensive unchecked
// indexing and the array sizes were not known at compile time, so it was a
// refactor away from potential memory unsafety. It also assumed big endian
// order, and on most systems our data is in little endian order.

/// Unsigned, little-endian, n-digit division with remainder
///
/// # Panics
///
/// Panics if divisor is zero
#[inline]
pub fn div_rem_big<const N: usize>(
    numerator: &[ULimb; N],
    divisor: &[ULimb; N],
) -> ([ULimb; N], [ULimb; N]) {
    if is_zero(numerator, 0) {
        return ([0; N], [0; N]);
    }

    // TODO: Make it M/N for the sizes
    match cmp(numerator, divisor) {
        Ordering::Less => ([0; N], *numerator),
        Ordering::Equal => {
            let mut quo = [0; N];
            quo[0] = 1;
            (quo, [0; N])
        },
        Ordering::Greater => {
            let n = last_index(divisor);
            if n == 0 {
                div_rem_small_padded(numerator, divisor[0])
            } else {
                let m = last_index(numerator) - n;
                div_rem_knuth(numerator, divisor, n + 1, m)
            }
        },
    }
}

/// Efficiently, const comparison of M to N sized arrays.
#[inline]
#[allow(clippy::comparison_chain)] // reason = "cannot use Ord since `cmp` isn't stable for primitives."
pub const fn cmp<const M: usize, const N: usize>(lhs: &[ULimb; M], rhs: &[ULimb; N]) -> Ordering {
    // Assume we have more limbs in lhs
    if M < N {
        return cmp(rhs, lhs).reverse();
    }

    // if lhs is larger with digits set, then always true
    let mut i = M;
    while i > N {
        i -= 1;
        if lhs[i] > 0 {
            return Ordering::Greater;
        }
    }
    while i > 0 {
        i -= 1;
        if lhs[i] > rhs[i] {
            return Ordering::Greater;
        } else if lhs[i] < rhs[i] {
            return Ordering::Less;
        }
    }

    Ordering::Equal
}

/// Check if all limbs are 0. Does not short-circuit.
///
/// Since we work with small versions of N, this can vectorize nicely
/// using packed comparisons. Use `i` as an offset since we can't use
/// range indexingg in `const` functions.
#[inline(always)]
const fn is_zero<const N: usize>(x: &[ULimb; N], mut i: usize) -> bool {
    let mut zero = true;
    while i < N {
        zero &= x[i] == 0;
        i += 1;
    }
    zero
}

/// Get the index of the first non-zero digit, from the MSB.
#[inline(always)]
const fn last_index<const N: usize>(x: &[ULimb; N]) -> usize {
    let mut i = N;
    while i > 0 {
        i -= 1;
        if x[i] != 0 {
            return i;
        }
    }
    0
}

/// Division of numerator by a u64 divisor
#[inline]
pub fn div_rem_small_padded<const M: usize, const N: usize>(
    numerator: &[ULimb; M],
    divisor: ULimb,
) -> ([ULimb; M], [ULimb; N]) {
    let (numerator, rem) = div_rem_small(numerator, divisor);
    let mut rem_padded = [0; N];
    rem_padded[0] = rem;
    (numerator, rem_padded)
}

/// Division of numerator by a u64 divisor
#[inline]
pub fn div_rem_small<const M: usize>(
    numerator: &[ULimb; M],
    divisor: ULimb,
) -> ([ULimb; M], ULimb) {
    let mut numerator = *numerator;
    let mut r = 0;
    let mut i = M;
    while i > 0 {
        i -= 1;
        let d = numerator[i];
        let (q, ri) = div_rem_word(r, d, divisor);
        numerator[i] = q;
        r = ri;
    }

    (numerator, r)
}

/// Use Knuth Algorithm D to compute `numerator / divisor` returning the
/// quotient and remainder
///
/// `n` is the number of non-zero 64-bit words in `divisor`
/// `m` is the number of non-zero 64-bit words present in `numerator` beyond
/// `divisor`, and therefore the number of words in the quotient
///
/// A good explanation of the algorithm can be found [here](https://ridiculousfish.com/blog/posts/labor-of-division-episode-iv.html)
#[inline]
fn div_rem_knuth<const N: usize>(
    numerator: &[ULimb; N],
    divisor: &[ULimb; N],
    n: usize,
    m: usize,
) -> ([ULimb; N], [ULimb; N]) {
    assert!(n + m <= N);

    // TODO: FIXME, see if we can make it M/N

    // The algorithm works by incrementally generating guesses `q_hat`, for the next
    // digit of the quotient, starting from the most significant digit.
    //
    // This relies on the property that for any `q_hat` where
    //
    //      (q_hat << (j * 64)) * divisor <= numerator`
    //
    // We can set
    //
    //      q += q_hat << (j * 64)
    //      numerator -= (q_hat << (j * 64)) * divisor
    //
    // And then iterate until `numerator < divisor`

    // We normalize the divisor so that the highest bit in the highest digit of the
    // divisor is set, this ensures our initial guess of `q_hat` is at most 2 off
    // from the correct value for q[j]
    let shift = divisor[n - 1].leading_zeros();
    // As the shift is computed based on leading zeros, don't need to perform
    // full_shl
    let divisor = shl_word(divisor, shift);
    // numerator may have fewer leading zeros than divisor, so must add another
    // digit
    let mut numerator = full_shl(numerator, shift);

    // The two most significant digits of the divisor
    let b0 = divisor[n - 1];
    let b1 = divisor[n - 2];

    let mut q = [0; N];

    let mut j = m + 1;
    while j > 0 {
        j -= 1;
        let a0 = numerator.get(j + n);
        let a1 = numerator.0[j + n - 1];

        let mut q_hat = if a0 < b0 {
            // The first estimate is [a1, a0] / b0, it may be too large by at most 2
            let (mut q_hat, mut r_hat) = div_rem_word(a0, a1, b0);

            // r_hat = [a1, a0] - q_hat * b0
            //
            // Now we want to compute a more precise estimate [a2,a1,a0] / [b1,b0]
            // which can only be less or equal to the current q_hat
            //
            // q_hat is too large if:
            // [a2,a1,a0] < q_hat * [b1,b0]
            // [a2,r_hat] < q_hat * b1
            let a2 = numerator.0[j + n - 2];
            let r = (q_hat as UWide) * (b1 as UWide);
            let (lo, hi) = (r as ULimb, (r >> ULimb::BITS) as ULimb);
            if (hi, lo) > (r_hat, a2) {
                q_hat -= 1;
                let (new_r_hat, overflow) = r_hat.overflowing_add(b0);
                r_hat = new_r_hat;

                if !overflow {
                    let r = (q_hat as UWide) * (b1 as UWide);
                    let (lo, hi) = (r as ULimb, (r >> ULimb::BITS) as ULimb);
                    if (hi, lo) > (r_hat, a2) {
                        q_hat -= 1;
                    }
                }
            }
            q_hat
        } else {
            ULimb::MAX
        };

        // q_hat is now either the correct quotient digit, or in rare cases 1 too large

        // Compute numerator -= (q_hat * divisor) << (j * 64)
        let mut i = 0;
        let mut c = false;
        let q_hat_v = full_mul_u64(&divisor, q_hat);
        while i < n + 1 {
            let x = numerator.get(i + j);
            let y = q_hat_v.get(i);
            let (res1, overflow1) = y.overflowing_add(c as ULimb);
            let (res2, overflow2) = x.overflowing_sub(res1);
            numerator.set(i + j, res2);
            c = overflow1 || overflow2;
            i += 1
        }

        // If underflow, q_hat was too large by 1
        if c {
            // Reduce q_hat by 1
            q_hat -= 1;

            // Add back one multiple of divisor
            i = 0;
            c = false;
            while i < n + 1 {
                let x = numerator.get(i + j);
                let y = divisor[i];
                let (res1, overflow1) = y.overflowing_add(c as ULimb);
                let (res2, overflow2) = x.overflowing_add(res1);
                numerator.set(i + j, res2);
                c = overflow1 || overflow2;
                i += 1
            }
            let value = numerator.get(j + n).wrapping_add(c as ULimb);
            numerator.set(j + n, value);
        }

        // q_hat is the correct value for q[j]
        q[j] = q_hat;
    }

    // The remainder is what is left in numerator, with the initial normalization
    // shl reversed
    let remainder = full_shr(&numerator, shift);
    (q, remainder)
}

/// Perform narrowing division of a u128 by a u64 divisor, returning the
/// quotient and remainder
///
/// This method may trap or panic if hi >= divisor, i.e. the quotient would not
/// fit into a 64-bit integer.
///
/// Using [`num::NonZero`] would allow significant optimizations on non-x86
/// architectures, however, it would be undefined behavior and would require
/// non-0 checks all the way up or have UB, a recipe for disaster.
#[inline(always)]
fn div_rem_word(hi: ULimb, lo: ULimb, divisor: ULimb) -> (ULimb, ULimb) {
    debug_assert!(hi < divisor);
    debug_assert!(divisor != 0);

    // NOTE: ARM64 requires the `__udivti3` Clang instrinsic internally,
    // which means we get 0 optimizations which our own implementation,
    // well, maybe besides a 0-divisor check.

    // LLVM fails to use the div instruction as it is not able to prove
    // that hi < divisor, and therefore the result will fit into 64-bits
    // SAFETY: Safe since we've validated the parameters.
    #[cfg(all(target_arch = "x86_64"))]
    unsafe {
        let mut quot = lo;
        let mut rem = hi;
        core::arch::asm!(
            "div {divisor}",
            divisor = in(reg) divisor,
            inout("rax") quot,
            inout("rdx") rem,
            options(pure, nomem, nostack)
        );
        (quot, rem)
    }

    #[cfg(not(target_arch = "x86_64"))]
    {
        let x = ((hi as UWide) << ULimb::BITS) + (lo as UWide);
        let y = divisor as UWide;
        ((x / y) as ULimb, (x % y) as ULimb)
    }
}

/// Widening multiplication of an N-digit array with a u64
#[inline(always)]
const fn full_mul_u64<const N: usize>(a: &[ULimb; N], b: ULimb) -> ArrayPlusOne<N> {
    let mut out = [0; N];
    let mut carry = 0;
    let mut i = 0;
    while i < N {
        let v = a[i];
        let r = v as UWide * b as UWide + carry as UWide;
        out[i] = r as ULimb;
        carry = (r >> ULimb::BITS) as ULimb;
        i += 1;
    }
    ArrayPlusOne(out, carry)
}

/// Left shift of an N-digit array by at most 63 bits
#[inline(always)]
const fn shl_word<const N: usize>(v: &[ULimb; N], shift: u32) -> [ULimb; N] {
    full_shl(v, shift).0
}

/// Widening left shift of an N-digit array by at most 63 bits
#[inline(always)]
const fn full_shl<const N: usize>(v: &[ULimb; N], shift: u32) -> ArrayPlusOne<N> {
    debug_assert!(shift < ULimb::BITS);
    if shift == 0 {
        return ArrayPlusOne(*v, 0);
    }
    let mut out = [0; N];
    out[0] = v[0] << shift;
    let mut i = 1;
    while i < N {
        out[i] = v[i - 1] >> (ULimb::BITS - shift) | v[i] << shift;
        i += 1;
    }
    let carry = v[N - 1] >> (ULimb::BITS - shift);
    ArrayPlusOne(out, carry)
}

/// Narrowing right shift of an (N+1)-digit array by at most 63 bits
#[inline(always)]
const fn full_shr<const N: usize>(a: &ArrayPlusOne<N>, shift: u32) -> [ULimb; N] {
    debug_assert!(shift < ULimb::BITS);
    if shift == 0 {
        return a.0;
    }
    let mut out = [0; N];
    let mut i = 0;
    while i < N - 1 {
        out[i] = a.0[i] >> shift | a.0[i + 1] << (ULimb::BITS - shift);
        i += 1;
    }
    out[N - 1] = a.0[N - 1] >> shift;
    out
}

/// An array of N + 1 elements
///
/// This is a hack around lack of support for const arithmetic
#[repr(C)]
struct ArrayPlusOne<const N: usize>([ULimb; N], ULimb);

impl<const N: usize> ArrayPlusOne<N> {
    #[inline(always)]
    const fn get(&self, index: usize) -> ULimb {
        if index == N {
            self.1
        } else {
            self.0[index]
        }
    }

    #[inline(always)]
    fn set(&mut self, index: usize, value: ULimb) {
        if index == N {
            self.1 = value;
        } else {
            self.0[index] = value;
        }
    }
}
