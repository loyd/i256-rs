#[macro_use]
mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use i256::math::{sub_u128, sub_u32, sub_u64};

const COUNT: usize = 10000;

native_op!(u32, u64, sub_u32_native, wrapping_sub);
native_op!(u64, u128, sub_u64_native, wrapping_sub);

fn sub_random(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("sub");
    group.measurement_time(Duration::from_secs(5));

    let seed = fastrand::u64(..);
    let u32_data = gen_numbers!(u32, COUNT, seed);
    let u64_data = gen_numbers!(u64, COUNT, seed);
    let u128_data = gen_numbers!(u128, COUNT, seed);

    op_generator!(group, "u32-i256", sub_u32, u32_data.iter());
    op_generator!(group, "u32-native", sub_u32_native, u32_data.iter());
    op_generator!(group, "u64-i256", sub_u64, u64_data.iter());
    op_generator!(group, "u64-native", sub_u64_native, u64_data.iter());
    op_generator!(group, "u128-i256", sub_u128, u128_data.iter());
}

criterion_group!(sub_random_benches, sub_random);
criterion_main!(sub_random_benches);
