#[macro_use]
mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use input::*;

macro_rules! add_group {
    ($name:ident, $strategy:expr, $prefix:literal) => {
        fn $name(criterion: &mut Criterion) {
            let mut group = criterion.benchmark_group("rotate");
            group.measurement_time(Duration::from_secs(5));

            let seed = fastrand::u64(..);
            let mut rng = fastrand::Rng::with_seed(seed);

            let bnum_data: Vec<(Bnum256, u32)> =
                u128::gen_n::<3>($strategy, &mut rng, DEFAULT_COUNT)
                    .iter()
                    .map(|x| (to_bnum(x[0], x[1]), x[2] as u32))
                    .collect();
            let i256_data: Vec<(u256, u32)> = u128::gen_n::<3>($strategy, &mut rng, DEFAULT_COUNT)
                .iter()
                .map(|x| (u256::new(x[0], x[1]), x[2] as u32))
                .collect();

            add_bench!(group, concat!($prefix, "::bnum-left"), bnum_data.iter(), |x: &(
                Bnum256,
                u32
            )| x
                .0
                .rotate_left(x.1));

            add_bench!(group, concat!($prefix, "::i256-left"), i256_data.iter(), |x: &(
                u256,
                u32
            )| x
                .0
                .rotate_left(x.1));

            add_bench!(group, concat!($prefix, "::bnum-right"), bnum_data.iter(), |x: &(
                Bnum256,
                u32
            )| x
                .0
                .rotate_right(x.1));

            add_bench!(group, concat!($prefix, "::i256-right"), i256_data.iter(), |x: &(
                u256,
                u32
            )| x
                .0
                .rotate_right(x.1));
        }
    };
}

add_group!(rotate_uniform, RandomGen::Uniform, "uniform");
add_group!(rotate_simple, RandomGen::Simple, "simple");
add_group!(rotate_large, RandomGen::Large, "large");

criterion_group!(rotate_random_benches, rotate_uniform, rotate_simple, rotate_large);
criterion_main!(rotate_random_benches);
