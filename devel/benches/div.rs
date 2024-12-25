#[macro_use]
mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use input::*;

// Just chosen from a fixed point, first 4 digits of pi.
const DIV_FACTOR: u64 = 3141;

macro_rules! add_group {
    ($name:ident, $strategy:expr, $prefix:literal) => {
        fn $name(criterion: &mut Criterion) {
            let mut group = criterion.benchmark_group("div");
            group.measurement_time(Duration::from_secs(5));

            let seed = fastrand::u64(..);
            let mut rng = fastrand::Rng::with_seed(seed);
            add_benches!(group, $strategy, rng, $prefix, checked_div);

            let wide_data = get_wide_data($strategy, &mut rng);
            add_bench!(group, concat!($prefix, "::u256-wide"), wide_data.iter(), |x: &(
                u256,
                u128
            )| x
                .0
                .checked_div_uwide(x.1));

            let limb_data = get_limb_data($strategy, &mut rng);
            add_bench!(group, concat!($prefix, "::u256-limb"), limb_data.iter(), |x: &(
                u256,
                u64
            )| x
                .0
                .checked_div_ulimb(x.1));

            add_bench!(group, concat!($prefix, "::u256-limb-const"), limb_data.iter(), |x: &(
                u256,
                u64
            )| x
                .0
                .checked_div_ulimb(DIV_FACTOR));
        }
    };
}

add_group!(div_uniform, RandomGen::Uniform, "uniform");
add_group!(div_simple, RandomGen::Simple, "simple");
add_group!(div_large, RandomGen::Large, "large");

criterion_group!(div_random_benches, div_uniform, div_simple, div_large);
criterion_main!(div_random_benches);
