# i256

Optimized implementations of 256-bit signed and unsigned integers.

This contains a fixed-width, performant implementation for 256-bit
signed and unsigned integers. This has significantly faster performance
for basic math operations than comparable fixed-width integer types,
since it can use optimizations from 128-bit integers on 64-bit
architectures.

## Versioning and Version Support

**Rustc Compatibility**

- `i256` currently supports 1.59+, including stable, beta, and nightly. This aims to support at least the Rust included in the latest stable Debian release.

Please report any errors compiling a supported `i256` version on a compatible Rustc version.

**Versioning**

`i256` uses [semantic versioning](https://semver.org/). Removing support for Rustc versions newer than the latest stable Debian or Ubuntu version is considered an incompatible API change, requiring a major (minor pre-1.0) version change.

## Changelog

All changes are documented in [CHANGELOG](https://github.com/Alexhuszagh/i256/blob/main/CHANGELOG).

## License

`i256` is dual licensed under the Apache 2.0 license as well as the MIT license.

Almost all of the accessory methods in [ints](/src/ints/), such as the `checked_*`, `unchecked_*`, `strict_*`, and others, including their documentation, are taken directly from the Rust implementation, specifically, [`uint_macros`] and [`int_macros`]. The core algorithms under [math](/src/math/) for numeric operations, both their wrapping and overflowing forms, are not.

[`uint_macros`]: https://github.com/rust-lang/rust/blob/master/library/core/src/num/uint_macros.rs
[`int_macros`]: https://github.com/rust-lang/rust/blob/master/library/core/src/num/int_macros.rs

## Contributing

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in i256 by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions. Contributing to the repository means abiding by the [code of conduct](https://github.com/Alexhuszagh/i256/blob/main/CODE_OF_CONDUCT.md).
