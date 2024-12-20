#![allow(clippy::disallowed_macros)]

#[allow(arithmetic_overflow)]
fn overflow() {
    let _ = 255_u8 + 1;
}

fn main() {
    let metadata = rustc_version::version_meta().unwrap();
    if metadata.channel == rustc_version::Channel::Nightly {
        println!("cargo:rustc-cfg=is_nightly");
    }

    // NOTE: although it's less than ideal, we also use debug_assertions
    // since there is no stable way to check if there's overflow checks.
    if std::panic::catch_unwind(overflow).is_err() {
        println!("cargo:rustc-cfg=have_overflow_checks");
    }
}
