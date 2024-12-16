#[macro_use]
mod input;

use core::time::Duration;

use criterion::{criterion_group, criterion_main, Criterion};
use i256::math::{add_u128, add_u32, add_u64};

const COUNT: usize = 10000;

native_op!(u32, u64, add_u32_native, wrapping_add);
native_op!(u64, u128, add_u64_native, wrapping_add);

fn add_random(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("add");
    group.measurement_time(Duration::from_secs(5));

    let seed = fastrand::u64(..);
    let u32_data = gen_numbers!(u32, COUNT, seed);
    let u64_data = gen_numbers!(u64, COUNT, seed);
    let u128_data = gen_numbers!(u128, COUNT, seed);

    op_generator!(group, "u32-i256", add_u32, u32_data.iter());
    op_generator!(group, "u32-native", add_u32_native, u32_data.iter());
    op_generator!(group, "u64-i256", add_u64, u64_data.iter());
    op_generator!(group, "u64-native", add_u64_native, u64_data.iter());
    op_generator!(group, "u128-i256", add_u128, u128_data.iter());
}

criterion_group!(add_random_benches, add_random);
criterion_main!(add_random_benches);
