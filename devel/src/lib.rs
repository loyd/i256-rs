// NOTE: We use this for our ASM analysis, which can be done via:
//      cargo +nightly rustc --release -- --emit asm

#[no_mangle]
pub const fn mul_signed_bnum(x: bnum::types::I256, y: bnum::types::I256) -> bnum::types::I256 {
    x.wrapping_mul(y)
}

#[no_mangle]
pub const fn mul_unsigned_bnum(x: bnum::types::U256, y: bnum::types::U256) -> bnum::types::U256 {
    x.wrapping_mul(y)
}

#[no_mangle]
pub const fn mul_signed_i256(x: i256::i256, y: i256::i256) -> i256::i256 {
    x.wrapping_mul(y)
}

#[no_mangle]
pub const fn mul_unsigned_i256(x: i256::u256, y: i256::u256) -> i256::u256 {
    x.wrapping_mul(y)
}

#[no_mangle]
pub const fn overflowing_mul_signed_bnum(
    x: bnum::types::I256,
    y: bnum::types::I256,
) -> (bnum::types::I256, bool) {
    x.overflowing_mul(y)
}

#[no_mangle]
pub const fn overflowing_mul_signed_i256(x: i256::u256, y: i256::u256) -> (i256::u256, bool) {
    x.overflowing_mul(y)
}
