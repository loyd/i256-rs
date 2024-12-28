//! This tests the optimization of 3 different variants of bitwise
//! operation algorithms.

#[macro_use]
mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use input::*;

const COUNT: usize = 50000;

#[inline(always)]
pub const fn count_ones_u128(x: u128, y: u128) -> u32 {
    y.count_ones() + x.count_ones()
}

#[inline(always)]
pub const fn count_ones_u64(x: &[u64; 4]) -> u32 {
    let mut count = 0;
    let mut i = 0;
    while i < x.len() {
        count += x[i].count_ones();
        i += 1;
    }
    count
}

#[inline(always)]
pub const fn leading_zeros_u128(x: u128, y: u128) -> u32 {
    let mut leading = y.leading_zeros();
    if leading == 128 {
        leading += x.leading_zeros();
    }
    leading
}

#[inline(always)]
pub const fn leading_zeros_u64(x: &[u64; 4]) -> u32 {
    let mut count = 0;
    let mut i = 0;
    while i < x.len() && count as usize == i * 64 {
        count += x[x.len() - i - 1].leading_zeros();
        i += 1;
    }
    count
}

macro_rules! count_ones_group {
    ($name:ident, $strategy:expr, $prefix:literal) => {
        fn $name(criterion: &mut Criterion) {
            let mut group = criterion.benchmark_group("leading-zeros");
            group.measurement_time(Duration::from_secs(5));

            let seed = fastrand::u64(..);
            let mut rng = fastrand::Rng::with_seed(seed);
            let u128_data = u128::gen_n::<2>($strategy, &mut rng, COUNT);
            let u64_data = u64::gen_n::<4>($strategy, &mut rng, COUNT);

            add_bench!(group, concat!($prefix, "::u128"), u128_data.iter(), |x: &[u128; 2]| {
                count_ones_u128(x[0], x[1])
            });
            add_bench!(group, concat!($prefix, "::u64"), u64_data.iter(), count_ones_u64);
        }
    };
}

macro_rules! leading_zeros_group {
    ($name:ident, $strategy:expr, $prefix:literal) => {
        fn $name(criterion: &mut Criterion) {
            let mut group = criterion.benchmark_group("count-ones");
            group.measurement_time(Duration::from_secs(5));

            let seed = fastrand::u64(..);
            let mut rng = fastrand::Rng::with_seed(seed);
            let u128_data = u128::gen_n::<2>($strategy, &mut rng, COUNT);
            let u64_data = u64::gen_n::<4>($strategy, &mut rng, COUNT);

            add_bench!(group, concat!($prefix, "::u128"), u128_data.iter(), |x: &[u128; 2]| {
                leading_zeros_u128(x[0], x[1])
            });
            add_bench!(group, concat!($prefix, "::u64"), u64_data.iter(), leading_zeros_u64);
        }
    };
}

count_ones_group!(count_ones_uniform, RandomGen::Uniform, "uniform");
count_ones_group!(count_ones_simple, RandomGen::Simple, "simple");
count_ones_group!(count_ones_large, RandomGen::Large, "large");
criterion_group!(
    count_ones_random_benches,
    count_ones_uniform,
    count_ones_simple,
    count_ones_large
);

leading_zeros_group!(leading_zeros_uniform, RandomGen::Uniform, "uniform");
leading_zeros_group!(leading_zeros_simple, RandomGen::Simple, "simple");
leading_zeros_group!(leading_zeros_large, RandomGen::Large, "large");
criterion_group!(
    leading_zeros_random_benches,
    leading_zeros_uniform,
    leading_zeros_simple,
    leading_zeros_large
);

criterion_main!(count_ones_random_benches, leading_zeros_random_benches);
