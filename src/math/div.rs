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
//! Implementation heavily inspired by [`uint`]. Derived from
//! [`arrow`] and modified for certain optimizations and
//! enhancements.
//!
//! [`uint`]: https://github.com/paritytech/parity-common/blob/d3a9327124a66e52ca1114bb8640c02c18c134b8/uint/src/uint.rs#L844
//! [`arrow`]: https://github.com/apache/arrow-rs/blob/fcf4aa4c/arrow-buffer/src/bigint/div.rs

use core::cmp::Ordering;

use crate::types::{ULimb, UWide};

// NOTE: This cannot be made `const`, nor should it be attempted to be made so.
// We had a Knuth division algorithm previously in lexical, but it was removed
// for a few reasons, so we prioritize this. It used extensive unchecked
// indexing and the array sizes were not known at compile time, so it was a
// refactor away from potential memory unsafety. It also assumed big endian
// order, and on most systems our data is in little endian order.

/// Unsigned, little-endian, n-digit division with remainder.
///
/// # Panics
///
/// Panics if divisor is zero.
#[inline]
pub fn full<const M: usize, const N: usize>(
    numerator: &[ULimb; M],
    divisor: &[ULimb; N],
) -> ([ULimb; M], [ULimb; N]) {
    if N == 1 {
        return limb_padded(numerator, divisor[0]);
    }

    match cmp(numerator, divisor) {
        Ordering::Less => ([0; M], truncate(*numerator)),
        Ordering::Equal => (scalar1(1), scalar1(0)),
        Ordering::Greater => {
            if is_zero(numerator, 0) {
                (scalar1(0), scalar1(0))
            } else {
                full_gt(numerator, divisor)
            }
        },
    }
}

/// Division of a numerator by a u128 divisor.
///
/// Performance of this is highly variable: for small
/// divisors it can be very fast, for larger divisors
/// due to the creation of the temporary divisor it
/// can be significantly slower.
#[inline]
pub fn wide<const M: usize>(numerator: &[ULimb; M], divisor: UWide) -> ([ULimb; M], UWide) {
    // NOTE: It's way better to keep this optimization outside the comparison.
    if M >= 2 && is_zero(numerator, 2) {
        // Can do as a scalar operation, simple.
        if numerator[0] == 0 && numerator[1] == 0 {
            return (scalar1(0), 0);
        } else {
            let lo = numerator[0] as UWide;
            let hi = (numerator[1] as UWide) << ULimb::BITS;
            let numerator = lo | hi;
            let (quo, rem) = (numerator / divisor, numerator % divisor);
            return (scalar2(quo), rem);
        }
    }

    let y = scalar2::<2>(divisor);
    let (quo, rem) = match cmp(numerator, &y) {
        Ordering::Less => ([0; M], truncate(*numerator)),
        Ordering::Equal => return (scalar1(1), 0),
        Ordering::Greater => full_gt(numerator, &y),
    };
    let rem = (rem[0] as UWide) | ((rem[1] as UWide) << ULimb::BITS);

    (quo, rem)
}

/// Implementation like above, except considering we might have 4 values.
#[inline]
#[cfg(feature = "stdint")]
#[allow(clippy::assertions_on_constants)]
pub fn from_u128<const M: usize>(numerator: &[ULimb; M], divisor: u128) -> ([ULimb; M], u128) {
    assert!(ULimb::BITS == 32);

    // NOTE: It's way better to keep this optimization outside the comparison.
    if M >= 2 && is_zero(numerator, 2) {
        // Can do as a scalar operation, simple.
        if numerator[0] == 0 && numerator[1] == 0 {
            return (scalar1(0), 0);
        } else {
            let numerator = u128_scalar(numerator);
            let (quo, rem) = (numerator / divisor, numerator % divisor);
            return (scalar_u128(quo), rem);
        }
    }

    let y = scalar_u128::<M>(divisor);
    let (quo, rem) = match cmp(numerator, &y) {
        Ordering::Less => ([0; M], truncate(*numerator)),
        Ordering::Equal => return (scalar1(1), 0),
        Ordering::Greater => full_gt(numerator, &y),
    };
    let rem = u128_scalar(&rem);

    (quo, rem)
}

/// Division of numerator by a u64 divisor
#[inline]
pub fn limb<const M: usize>(numerator: &[ULimb; M], divisor: ULimb) -> ([ULimb; M], ULimb) {
    // quick path optinmization for small values
    if M >= 2 && is_zero(numerator, 2) {
        let lo = numerator[0] as UWide;
        let hi = (numerator[1] as UWide) << ULimb::BITS;
        let numerator = lo | hi;
        let divisor = divisor as UWide;
        let (quo, rem) = (numerator / divisor, numerator % divisor);
        return (scalar2(quo), rem as ULimb);
    }

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

/// Internal variant that assumes our numerator >= divisor,
/// and therefore removes all validation checks.
#[inline]
fn full_gt<const M: usize, const N: usize>(
    numerator: &[ULimb; M],
    divisor: &[ULimb; N],
) -> ([ULimb; M], [ULimb; N]) {
    let n = last_index(divisor);
    if n == 0 {
        limb_padded(numerator, divisor[0])
    } else {
        let m = last_index(numerator) - n;
        div_rem_knuth(numerator, divisor, n + 1, m)
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

/// Construct an array from a limb.
#[inline(always)]
pub const fn scalar1<const N: usize>(value: ULimb) -> [ULimb; N] {
    assert!(N > 0);
    let mut r = [0; N];
    r[0] = value;
    r
}

/// Construct an array from a wide limb.
#[inline(always)]
pub const fn scalar2<const N: usize>(value: UWide) -> [ULimb; N] {
    assert!(N > 0);
    let mut r = [0; N];
    r[0] = value as ULimb;
    r[1] = (value >> ULimb::BITS) as ULimb;
    r
}

/// Construct an array from a u128 value. Only used for 32-bit ISAs.
#[inline(always)]
#[cfg(feature = "stdint")]
#[allow(clippy::assertions_on_constants)]
pub const fn scalar_u128<const N: usize>(value: u128) -> [ULimb; N] {
    assert!(N >= 4);
    assert!(ULimb::BITS == 32);

    let mut r = [0; N];
    r[0] = value as ULimb;
    r[1] = (value >> 32) as ULimb;
    r[2] = (value >> 64) as ULimb;
    r[3] = (value >> 96) as ULimb;
    r
}

/// Construct an array from a u128 value. Only used for 32-bit ISAs.
#[inline(always)]
#[cfg(feature = "stdint")]
#[allow(clippy::assertions_on_constants)]
pub const fn u128_scalar<const N: usize>(value: &[ULimb; N]) -> u128 {
    assert!(N >= 4);
    assert!(ULimb::BITS == 32);

    let x0 = value[0] as u128;
    let x1 = (value[1] as u128) << 32;
    let x2 = (value[2] as u128) << 64;
    let x3 = (value[3] as u128) << 96;

    x0 | x1 | x2 | x3
}

/// Division of numerator by a u64 divisor
#[inline]
pub fn limb_padded<const M: usize, const N: usize>(
    numerator: &[ULimb; M],
    divisor: ULimb,
) -> ([ULimb; M], [ULimb; N]) {
    let (numerator, rem) = limb(numerator, divisor);
    (numerator, scalar1(rem))
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
fn div_rem_knuth<const M: usize, const N: usize>(
    numerator: &[ULimb; M],
    divisor: &[ULimb; N],
    n: usize,
    m: usize,
) -> ([ULimb; M], [ULimb; N]) {
    assert!(n + m <= M);

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

    let mut q = [0; M];

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
            i += 1;
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
                i += 1;
            }
            let value = numerator.get(j + n).wrapping_add(c as ULimb);
            numerator.set(j + n, value);
        }

        // q_hat is the correct value for q[j]
        q[j] = q_hat;
    }

    // The remainder is what is left in numerator, with the initial normalization
    // shl reversed
    let remainder = truncate(full_shr(&numerator, shift));
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

    // Using a naive implementation can have major performance impacts. For
    // small integers, the overhead can be ~70% slower. For large ones, it
    // can be 10-12% slower. For example, for the following cases, we got
    // the following bench results (5K ints per benchmark).
    // Uniform:
    // - naive: 203.68 µs
    // - divq: 188.65 µs
    //
    // Simple:
    // - naive: 203.36 µs
    // - divq: 127.62 µs
    //
    // Large:
    // - naive: 206.92 µs
    // - divq: 189.52 µs

    // Manally implementation the `udiv128by64to64default` part of `udivti3`
    // did not lead to any performance gains, rather, serious regressions,
    // which might be due to optimization considerations.

    // NOTE: ARM64 requires the `__udivti3` Clang instrinsic internally,
    // which means we get 0 optimizations which our own implementation,
    // well, maybe besides a 0-divisor check. This already has heavy
    // fast-path optimizations when the divisor fits in 64 bits.

    // LLVM fails to use the div instruction as it is not able to prove
    // that hi < divisor, and therefore the result will fit into 64-bits
    // SAFETY: Safe since we've validated the parameters. This is
    // never UB, since providing a 0 divisor is valid and just leads
    // to a division [`error`](https://www.felixcloutier.com/x86/div).
    #[cfg(all(target_arch = "x86_64", not(feature = "noasm"), not(feature = "limb32")))]
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

    // NOTE: We've tried a lot to optimize this. Rust's codegen
    // or LLVM's intrinsics make this not worth it, in fact, every
    // attempt has backfired spectacularly. We've tried:
    // - https://github.com/ridiculousfish/libdivide/blob/af1db19/libdivide.h#L491
    // - https://codebrowser.dev/llvm/compiler-rt/lib/builtins/udivmodti4.c.html#22
    //
    // What we have is simple and fast.
    #[cfg(any(not(target_arch = "x86_64"), feature = "noasm", feature = "limb32"))]
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
        out[i] = (v[i - 1] >> (ULimb::BITS - shift)) | (v[i] << shift);
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
        out[i] = (a.0[i] >> shift) | (a.0[i + 1] << (ULimb::BITS - shift));
        i += 1;
    }
    out[N - 1] = a.0[N - 1] >> shift;
    out
}

/// Truncate the extra digits from the top of the array.
#[inline(always)]
pub const fn truncate<const M: usize, const N: usize>(v: [ULimb; M]) -> [ULimb; N] {
    assert!(M >= N);
    let mut r = [0; N];
    let mut i = 0;
    while i < N {
        r[i] = v[i];
        i += 1;
    }
    r
}

/// An array of N + 1 elements
///
/// This is a hack around lack of support for const arithmetic
///
/// The order of this isn't **GUARANTEED** to be te same order of
/// indexing.
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
