#[macro_use]
mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use input::*;

macro_rules! add_group {
    ($name:ident, $strategy:expr, $prefix:literal) => {
        fn $name(criterion: &mut Criterion) {
            let mut group = criterion.benchmark_group("div");
            group.measurement_time(Duration::from_secs(5));

            let seed = fastrand::u64(..);
            let mut rng = fastrand::Rng::with_seed(seed);
            add_benches!(group, $strategy, rng, $prefix, wrapping_div);

            let small_data = get_small_data($strategy, &mut rng);
            add_bench!(group, concat!($prefix, "::u256-small"), small_data.iter(), |x: &(
                u256,
                u128
            )| x
                .0
                .wrapping_div_small(x.1));

            let half_data = get_half_data($strategy, &mut rng);
            add_bench!(group, concat!($prefix, "::u256-half"), half_data.iter(), |x: &(
                u256,
                u64
            )| x
                .0
                .wrapping_div_half(x.1));
        }
    };
}

add_group!(div_uniform, RandomGen::Uniform, "uniform");
add_group!(div_simple, RandomGen::Simple, "simple");
add_group!(div_large, RandomGen::Large, "large");

criterion_group!(div_random_benches, div_uniform, div_simple, div_large);
criterion_main!(div_random_benches);
