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

lexical uses [semantic versioning](https://semver.org/). Removing support for Rustc versions newer than the latest stable Debian or Ubuntu version is considered an incompatible API change, requiring a major version change

## Changelog

All changes are documented in [CHANGELOG](https://github.com/Alexhuszagh/i256/blob/main/CHANGELOG).

## License

Lexical is dual licensed under the Apache 2.0 license as well as the MIT license.

## Contributing

Unless you explicitly state otherwise, any contribution intentionally submitted for inclusion in i256 by you, as defined in the Apache-2.0 license, shall be dual licensed as above, without any additional terms or conditions. Contributing to the repository means abiding by the [code of conduct](https://github.com/Alexhuszagh/i256/blob/main/CODE_OF_CONDUCT.md).
