#[macro_use]
mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use input::*;

const ADD_MARKER: u32 = 0x4000;
const UNIVERSAL: u32 = 0x3FFF;

#[inline(always)]
const fn hi(x: &i256::u256) -> i256::u256 {
    i256::u256::from_u128(x.get_wide(1))
}

#[inline(always)]
const fn lo(x: &i256::u256) -> i256::u256 {
    i256::u256::from_u128(x.get_wide(0))
}

#[inline(always)]
pub const fn mulhi(x: &i256::u256, y: &i256::u256) -> i256::u256 {
    // Extract high-and-low masks.
    let x1 = hi(x);
    let x0 = lo(x);
    let y1 = hi(y);
    let y0 = lo(y);

    let w0 = x0.wrapping_mul(y0);
    let m = x0.wrapping_mul(y1).wrapping_add(hi(&w0));
    let w1 = lo(&m);
    let w2 = hi(&m);

    let w3 = lo(&x1.wrapping_mul(y0).wrapping_add(w1));

    x1.wrapping_mul(y1).wrapping_add(w2).wrapping_add(w3)
}

// NOTE: This does not calculate the remainder
// NOTE: This is a PoC but we don't use this because it's not very fast.
#[inline]
const fn divide_by_num(num: &i256::u256, den: &i256::u256, more: u32) -> i256::u256 {
    if den.eq_const(i256::u256::from_u8(0)) {
        num.wrapping_shr(more as u32)
    } else {
        let mask = i256::u256::MAX;
        let q = mulhi(den, num);
        if more & ADD_MARKER != 0 {
            let t = num.wrapping_sub_ulimb(1).bitand_const(mask).wrapping_shr(1).wrapping_add(q);
            let t = t.bitand_const(mask);
            t.wrapping_shr(more & UNIVERSAL)
        } else {
            q.wrapping_shr(more)
        }
    }
}

#[inline]
const fn div_rem_by_num(num: &i256::u256, den: &i256::u256, more: u32) -> (i256::u256, i256::u256) {
    let quo = divide_by_num(num, den, more);
    let rem = num.wrapping_sub(quo.wrapping_mul(*den));
    (quo, rem)
}

macro_rules! add_group {
    ($name:ident, $strategy:expr, $prefix:literal) => {
        fn $name(criterion: &mut Criterion) {
            let mut group = criterion.benchmark_group("div");
            group.measurement_time(Duration::from_secs(5));

            let seed = fastrand::u64(..);
            let mut rng = fastrand::Rng::with_seed(seed);

            // unsigned
            let u128_udata = u128::gen_n::<4>($strategy, &mut rng, DEFAULT_COUNT);
            let u256_udata = to_u256_udata(&u128_udata);
            // this is exactly equal to a divisor of "10"
            let div10_magic = i256::u256::from_le_u64([
                0xcccccccccccccccd,
                0xcccccccccccccccc,
                0xcccccccccccccccc,
                0xcccccccccccccccc,
            ]);
            let div10_more = 3u32;
            // this is exactly equal to a divisor of "0x12345678"
            let div1234_magic = i256::u256::from_le_u64([
                0x112efe24120f7033,
                0xf2109855898d0ed7,
                0x8040021bc22011eb,
                0xe10000077880003f,
            ]);
            let div1234_more = 28u32;

            add_bench!(
                group,
                concat!($prefix, "::unsigned-256"),
                u256_udata.iter(),
                bench_op!(checked_div, i256::u256)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-256-div10"),
                u256_udata.iter(),
                |x: &(i256::u256, i256::u256)| x.0.checked_div_ulimb(10)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-256-mul10"),
                u256_udata.iter(),
                |x: &(i256::u256, i256::u256)| divide_by_num(&x.0, &div10_magic, div10_more)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-256-mul10-rem"),
                u256_udata.iter(),
                |x: &(i256::u256, i256::u256)| div_rem_by_num(&x.0, &div10_magic, div10_more)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-256-div0x12345678"),
                u256_udata.iter(),
                |x: &(i256::u256, i256::u256)| x.0.checked_div_ulimb(0x12345678)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-256-mul0x12345678"),
                u256_udata.iter(),
                |x: &(i256::u256, i256::u256)| divide_by_num(&x.0, &div1234_magic, div1234_more)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-256-mul0x12345678-rem"),
                u256_udata.iter(),
                |x: &(i256::u256, i256::u256)| div_rem_by_num(&x.0, &div1234_magic, div1234_more)
            );
        }
    };
}

add_group!(div_uniform, RandomGen::Uniform, "uniform");
add_group!(div_simple, RandomGen::Simple, "simple");
add_group!(div_large, RandomGen::Large, "large");

criterion_group!(div_random_benches, div_uniform, div_simple, div_large);
criterion_main!(div_random_benches);
