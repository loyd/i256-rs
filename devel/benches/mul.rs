#[macro_use]
mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use input::*;

macro_rules! add_group {
    ($name:ident, $strategy:expr, $prefix:literal) => {
        fn $name(criterion: &mut Criterion) {
            let mut group = criterion.benchmark_group("mul");
            group.measurement_time(Duration::from_secs(5));

            let seed = fastrand::u64(..);
            let mut rng = fastrand::Rng::with_seed(seed);
            add_benches!(group, $strategy, rng, $prefix, wrapping_mul);

            let wide_data = get_wide_data($strategy, &mut rng);
            add_bench!(group, concat!($prefix, "::u256-wide"), wide_data.iter(), |x: &(
                u256,
                u128
            )| x
                .0
                .wrapping_mul_uwide(x.1));

            let limb_data = get_limb_data($strategy, &mut rng);
            add_bench!(group, concat!($prefix, "::u256-limb"), limb_data.iter(), |x: &(
                u256,
                u64
            )| x
                .0
                .wrapping_mul_ulimb(x.1));
        }
    };
}

add_group!(mul_uniform, RandomGen::Uniform, "uniform");
add_group!(mul_simple, RandomGen::Simple, "simple");
add_group!(mul_large, RandomGen::Large, "large");

criterion_group!(mul_random_benches, mul_uniform, mul_simple, mul_large);
criterion_main!(mul_random_benches);
