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

            // unsigned
            let u128_udata = u128::gen_n::<3>($strategy, &mut rng, DEFAULT_COUNT);
            let bnum_udata: Vec<(BnumU256, u32)> =
                u128_udata.iter().map(|x| (to_bunum(x[0], x[1]), x[2] as u32)).collect();
            let u256_udata: Vec<(i256::u256, u32)> =
                u128_udata.iter().map(|x| (to_u256(x[0], x[1]), x[2] as u32)).collect();

            add_bench!(
                group,
                concat!($prefix, "::unsigned-bnum-left"),
                bnum_udata.iter(),
                bench_op!(rotate_left, BnumU256, u32)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-256-left"),
                u256_udata.iter(),
                bench_op!(rotate_left, i256::u256, u32)
            );

            add_bench!(
                group,
                concat!($prefix, "::unsigned-bnum-right"),
                bnum_udata.iter(),
                bench_op!(rotate_right, BnumU256, u32)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-256-right"),
                u256_udata.iter(),
                bench_op!(rotate_right, i256::u256, u32)
            );

            // signed
            let i128_idata = i128::gen_n::<3>($strategy, &mut rng, DEFAULT_COUNT);
            let bnum_idata: Vec<(BnumI256, u32)> =
                i128_idata.iter().map(|x| (to_binum(x[0], x[1]), x[2] as u32)).collect();
            let i256_idata: Vec<(i256::i256, u32)> =
                i128_idata.iter().map(|x| (to_i256(x[0], x[1]), x[2] as u32)).collect();

            add_bench!(
                group,
                concat!($prefix, "::signed-bnum-left"),
                bnum_idata.iter(),
                bench_op!(rotate_left, BnumI256, u32)
            );
            add_bench!(
                group,
                concat!($prefix, "::signed-256-left"),
                i256_idata.iter(),
                bench_op!(rotate_left, i256::i256, u32)
            );

            add_bench!(
                group,
                concat!($prefix, "::signed-bnum-right"),
                bnum_idata.iter(),
                bench_op!(rotate_right, BnumI256, u32)
            );
            add_bench!(
                group,
                concat!($prefix, "::signed-256-right"),
                i256_idata.iter(),
                bench_op!(rotate_right, i256::i256, u32)
            );
        }
    };
}

add_group!(rotate_uniform, RandomGen::Uniform, "uniform");
add_group!(rotate_simple, RandomGen::Simple, "simple");
add_group!(rotate_large, RandomGen::Large, "large");

criterion_group!(rotate_random_benches, rotate_uniform, rotate_simple, rotate_large);
criterion_main!(rotate_random_benches);
