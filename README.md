# Mersenne Twister in Rust

This is a pure rust port of the
[Mersenne Twister](http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/emt.html)
pseudorandom number generators. [See the rustdoc][doc] for suggested usage.

[doc]: https://dcrewi.github.io/rust-mersenne-twister/doc/0.3/mersenne_twister/index.html

## Algorithms

- MT19937 (32-bit version)
- MT19937-64 (64-bit version)

## Stability

All code and tests should compile and run without problems on all 1.x
versions of rust back to 1.0.0. The only exceptions is the
benchmarks, which is still an unstable feature as of rust 1.14. They
are optional though and the crate can be used without them.

## License

Licensed under either of
 * Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)
at your option.

### Contribution

Unless you explicitly state otherwise, any contribution intentionally
submitted for inclusion in the work by you, as defined in the
Apache-2.0 license, shall be dual licensed as above, without any
additional terms or conditions.
