#[macro_use]
mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use i256::math::{mul_u128, mul_u32, mul_u64};

const COUNT: usize = 10000;

native_op!(u32, u64, mul_u32_native, wrapping_mul);
native_op!(u64, u128, mul_u64_native, wrapping_mul);

fn mul_random(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("mul");
    group.measurement_time(Duration::from_secs(5));

    let seed = fastrand::u64(..);
    let u32_data = gen_numbers!(u32, COUNT, seed);
    let u64_data = gen_numbers!(u64, COUNT, seed);
    let u128_data = gen_numbers!(u128, COUNT, seed);

    op_generator!(group, "u32-i256", mul_u32, u32_data.iter());
    op_generator!(group, "u32-native", mul_u32_native, u32_data.iter());
    op_generator!(group, "u64-i256", mul_u64, u64_data.iter());
    op_generator!(group, "u64-native", mul_u64_native, u64_data.iter());
    op_generator!(group, "u128-i256", mul_u128, u128_data.iter());
}

criterion_group!(mul_random_benches, mul_random);
criterion_main!(mul_random_benches);
