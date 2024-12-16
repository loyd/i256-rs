use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use i256::math::{div_rem_big, div_rem_small};

const COUNT: usize = 10000;

macro_rules! gen_numbers {
    ($n:ident, $d:ident, $count:expr, $seed:ident) => {{
        let mut rng = fastrand::Rng::with_seed($seed);
        let mut vec: Vec<($n, $d)> = Vec::with_capacity($count);
        // TODO: Fix, this is wayyyy too likely to overflow
        // Going to need strategies
        while vec.len() < $count {
            let num = rng.$n(<$n>::MIN..<$n>::MAX);
            let den = rng.$d(<$d>::MIN..<$d>::MAX);
            if den != 0 {
                vec.push((num, den));
            }
        }
        vec
    }};
}

macro_rules! op_generator {
    ($group:ident, $name:expr, $func:ident, $iter:expr) => {{
        $group.bench_function($name, |bench| {
            bench.iter(|| {
                $iter.for_each(|&x| {
                    criterion::black_box($func(x.0, x.1));
                })
            })
        });
    }};
}

#[inline]
fn u128_div(num: u128, den: u128) -> (u128, u128) {
    let x0 = num as u64;
    let x1 = (num >> 64) as u64;
    let y0 = den as u64;
    let y1 = (den >> 64) as u64;

    let num = [x0, x1];
    let den = [y0, y1];
    let (div, rem) = div_rem_big(&num, &den);

    let x0 = div[0] as u128;
    let x1 = div[1] as u128;
    let y0 = rem[0] as u128;
    let y1 = rem[1] as u128;

    (x0 | x1 << 64, y0 | y1 << 64)
}

#[inline]
fn u128_div_small(num: u128, den: u64) -> (u128, u64) {
    let x0 = num as u64;
    let x1 = (num >> 64) as u64;

    let num = [x0, x1];
    let (div, rem) = div_rem_small(&num, den);

    let x0 = div[0] as u128;
    let x1 = div[1] as u128;

    (x0 | x1 << 64, rem)
}

#[inline]
fn u128_native(num: u128, den: u128) -> (u128, u128) {
    let div = num / den;
    let rem = num % den;
    (div, rem)
}

#[inline]
fn u128_small_native(num: u128, den: u64) -> (u128, u64) {
    let den = den as u128;
    let div = num / den;
    let rem = num % den;
    (div, rem as u64)
}

fn div_random(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("div");
    group.measurement_time(Duration::from_secs(5));

    let seed = fastrand::u64(..);
    let big_data = gen_numbers!(u128, u128, COUNT, seed);
    let small_data = gen_numbers!(u128, u64, COUNT, seed);

    op_generator!(group, "u128-big-i256", u128_div, big_data.iter());
    op_generator!(group, "u128-small-i256", u128_div_small, small_data.iter());
    op_generator!(group, "u128-big-native", u128_native, big_data.iter());
    op_generator!(group, "u128-small-native", u128_small_native, small_data.iter());
}

criterion_group!(div_random_benches, div_random);
criterion_main!(div_random_benches);
