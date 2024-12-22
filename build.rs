#![allow(clippy::disallowed_macros)]

#[allow(arithmetic_overflow)]
fn overflow() {
    let _ = 255_u8 + 1;
}

fn main() {
    // NOTE: although it's less than ideal, we also use debug_assertions
    // since there is no stable way to check if there's overflow checks.
    if std::panic::catch_unwind(overflow).is_err() {
        println!("cargo:rustc-cfg=have_overflow_checks");
    }
}
