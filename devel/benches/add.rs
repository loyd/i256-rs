#[macro_use]
mod input;

use core::time::Duration;

use bnum::types::U256;
use criterion::{criterion_group, criterion_main, Criterion};
use i256::math::{add_u128, add_u32, add_u64};

const COUNT: usize = 10000;

native_op!(u32, u64, add_u32_native, wrapping_add);
native_op!(u64, u128, add_u64_native, wrapping_add);

#[inline]
fn add_bnum(x: U256, y: U256) -> U256 {
    x.wrapping_add(y)
}

fn add_random(criterion: &mut Criterion) {
    let mut group = criterion.benchmark_group("add");
    group.measurement_time(Duration::from_secs(5));

    let seed = fastrand::u64(..);
    let u32_data = gen_numbers!(@4 u32, COUNT, seed);
    let u64_data = gen_numbers!(@4 u64, COUNT, seed);
    let u128_data = gen_numbers!(@4 u128, COUNT, seed);
    let bnum_data: Vec<(U256, U256)> = u128_data
        .iter()
        .map(|x| (input::bnum_from_u128(x.0, x.1), input::bnum_from_u128(x.2, x.3)))
        .collect();

    op_generator!(@4 group, "u32-i256", add_u32, u32_data.iter());
    op_generator!(@4 group, "u32-native", add_u32_native, u32_data.iter());
    op_generator!(@4 group, "u64-i256", add_u64, u64_data.iter());
    op_generator!(@4 group, "u64-native", add_u64_native, u64_data.iter());
    op_generator!(@4 group, "u128-i256", add_u128, u128_data.iter());
    op_generator!(@2 group, "u128-bnum", add_bnum, bnum_data.iter());
}

criterion_group!(add_random_benches, add_random);
criterion_main!(add_random_benches);
