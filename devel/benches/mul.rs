#[macro_use]
mod input;

use core::time::Duration;

use bnum::types::U256;
use criterion::{criterion_group, criterion_main, Criterion};
use i256::math::{mul_u128, mul_u32, mul_u64};

const COUNT: usize = 10000;

native_op!(u32, u64, mul_u32_native, wrapping_mul);
native_op!(u64, u128, mul_u64_native, wrapping_mul);

#[inline]
fn mul_bnum(x: U256, y: U256) -> U256 {
    x.wrapping_mul(y)
}

fn mul_random(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("mul");
    group.measurement_time(Duration::from_secs(5));

    let seed = fastrand::u64(..);
    let u32_data = gen_numbers!(@4 u32, COUNT, seed);
    let u64_data = gen_numbers!(@4 u64, COUNT, seed);
    let u128_data = gen_numbers!(@4 u128, COUNT, seed);
    let bnum_data: Vec<(U256, U256)> = u128_data
        .iter()
        .map(|x| (input::bnum_from_u128(x.0, x.1), input::bnum_from_u128(x.2, x.3)))
        .collect();

    op_generator!(@4 group, "u32-i256", mul_u32, u32_data.iter());
    op_generator!(@4 group, "u32-native", mul_u32_native, u32_data.iter());
    op_generator!(@4 group, "u64-i256", mul_u64, u64_data.iter());
    op_generator!(@4 group, "u64-native", mul_u64_native, u64_data.iter());
    op_generator!(@4 group, "u128-i256", mul_u128, u128_data.iter());
    op_generator!(@2 group, "u128-bnum", mul_bnum, bnum_data.iter());
}

criterion_group!(mul_random_benches, mul_random);
criterion_main!(mul_random_benches);
