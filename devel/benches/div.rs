#[macro_use]
mod input;

use core::time::Duration;

use bnum::types::U256;
use criterion::{criterion_group, criterion_main, Criterion};
use i256::math::div_rem_full;
use i256::u256;
use input::{NumberRng, RandomGen};

const COUNT: usize = 10000;

#[inline]
fn u128_div(num: u128, den: u128) -> (u128, u128) {
    if den == 0 {
        return (u128::MAX, 0);
    }
    let x0 = num as u64;
    let x1 = (num >> 64) as u64;
    let y0 = den as u64;
    let y1 = (den >> 64) as u64;

    let num = [x0, x1];
    let den = [y0, y1];
    let (div, rem) = div_rem_full(&num, &den);

    let x0 = div[0] as u128;
    let x1 = div[1] as u128;
    let y0 = rem[0] as u128;
    let y1 = rem[1] as u128;

    (x0 | x1 << 64, y0 | y1 << 64)
}

#[inline]
fn u128_native(num: u128, den: u128) -> (u128, u128) {
    if den == 0 {
        return (u128::MAX, 0);
    }
    let div = num / den;
    let rem = num % den;
    (div, rem)
}

#[inline]
fn i256_div(num: u256, den: u256) -> (u256, u256) {
    if den != u256::MIN {
        (num.wrapping_div(den), num.wrapping_rem(den))
    } else {
        (u256::MAX, u256::MIN)
    }
}

#[inline]
fn bnum_div(num: U256, den: U256) -> (U256, U256) {
    if den != U256::MIN {
        let div = num / den;
        let rem = num % den;
        (div, rem)
    } else {
        (U256::MAX, U256::MIN)
    }
}

#[inline]
fn i256_div_small(num: u256, den: u128) -> (u256, u128) {
    if den != u128::MIN {
        num.wrapping_div_rem_small(den)
    } else {
        (u256::MAX, u128::MIN)
    }
}

#[inline]
fn i256_div_half(num: u256, den: u64) -> (u256, u64) {
    if den != u64::MIN {
        num.wrapping_div_rem_half(den)
    } else {
        (u256::MAX, u64::MIN)
    }
}

macro_rules! div_bench {
    ($name:ident, $gen:ident, $prefix:literal) => {
        fn $name(criterion: &mut Criterion) {
            let mut group = criterion.benchmark_group("div");
            group.measurement_time(Duration::from_secs(5));

            let seed = fastrand::u64(..);
            let mut rng = fastrand::Rng::with_seed(seed);
            let full_data = u128::gen_n::<2>(RandomGen::$gen, &mut rng, COUNT);
            let u128_data = u128::gen_n::<4>(RandomGen::$gen, &mut rng, COUNT);
            let i256_data: Vec<[u256; 2]> =
                u128_data.iter().map(|x| [u256::new(x[0], x[1]), u256::new(x[2], x[3])]).collect();
            let bnum_data: Vec<[U256; 2]> = u128_data
                .iter()
                .map(|x| [input::bnum_from_u128(x[0], x[1]), input::bnum_from_u128(x[2], x[3])])
                .collect();

            let small = u128::gen_n::<1>(RandomGen::$gen, &mut rng, COUNT);
            let half = u64::gen_n::<1>(RandomGen::$gen, &mut rng, COUNT);
            let small_data: Vec<(u256, u128)> =
                i256_data.iter().zip(small.iter()).map(|(x, y)| (x[0], y[0])).collect();
            let half_data: Vec<(u256, u64)> =
                i256_data.iter().zip(half.iter()).map(|(x, y)| (x[0], y[0])).collect();

            op_generator!(@2 group, concat!($prefix, "::u128-full-i256"), u128_div, full_data.iter());
            op_generator!(@2tup group, concat!($prefix, "::u256-small-i256"), i256_div_small, small_data.iter());
            op_generator!(@2tup group, concat!($prefix, "::u256-half-i256"), i256_div_half, half_data.iter());

            op_generator!(@2 group, concat!($prefix, "::u128-full-native"), u128_native, full_data.iter());
            op_generator!(@2 group, concat!($prefix, "::u256-i256"), i256_div, i256_data.iter());
            op_generator!(@2 group, concat!($prefix, "::u256-bnum"), bnum_div, bnum_data.iter());
        }
    }
}

div_bench!(div_uniform, Uniform, "uniform");
div_bench!(div_simple, Simple, "simple");
div_bench!(div_large, Large, "large");

criterion_group!(div_random_benches, div_uniform, div_simple, div_large);
criterion_main!(div_random_benches);
