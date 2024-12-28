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

            // unsigned
            let u128_udata = u128::gen_n::<4>($strategy, &mut rng, DEFAULT_COUNT);
            let bnum_udata = to_bnum_udata(&u128_udata);
            let crypto_udata = to_crypto_udata(&u128_udata);
            let u256_udata = to_u256_udata(&u128_udata);
            let ulimb_udata = to_ulimb_udata(&u128_udata);

            add_bench!(
                group,
                concat!($prefix, "::unsigned-bnum"),
                bnum_udata.iter(),
                bench_op!(wrapping_mul, BnumU256)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-crypto"),
                crypto_udata.iter(),
                bench_op!(@ref wrapping_mul, CryptoU256)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-256"),
                u256_udata.iter(),
                bench_op!(wrapping_mul, i256::u256)
            );
            add_bench!(
                group,
                concat!($prefix, "::unsigned-256-ulimb"),
                ulimb_udata.iter(),
                bench_op!(wrapping_mul_ulimb, i256::u256, i256::ULimb)
            );

            // signed
            let i128_idata = i128::gen_n::<4>($strategy, &mut rng, DEFAULT_COUNT);
            let bnum_idata = to_bnum_idata(&i128_idata);
            let i256_idata = to_i256_idata(&i128_idata);
            let ulimb_idata = to_ulimb_idata(&i128_idata);
            let ilimb_idata = to_ilimb_idata(&i128_idata);

            add_bench!(
                group,
                concat!($prefix, "::signed-bnum"),
                bnum_idata.iter(),
                bench_op!(wrapping_mul, BnumI256)
            );
            add_bench!(
                group,
                concat!($prefix, "::signed-256"),
                i256_idata.iter(),
                bench_op!(wrapping_mul, i256::i256)
            );
            add_bench!(
                group,
                concat!($prefix, "::signed-256-ulimb"),
                ulimb_idata.iter(),
                bench_op!(wrapping_mul_ulimb, i256::i256, i256::ULimb)
            );
            add_bench!(
                group,
                concat!($prefix, "::signed-256-ilimb"),
                ilimb_idata.iter(),
                bench_op!(wrapping_mul_ilimb, i256::i256, i256::ILimb)
            );
        }
    };
}

add_group!(mul_uniform, RandomGen::Uniform, "uniform");
add_group!(mul_simple, RandomGen::Simple, "simple");
add_group!(mul_large, RandomGen::Large, "large");

criterion_group!(mul_random_benches, mul_uniform, mul_simple, mul_large);
criterion_main!(mul_random_benches);
