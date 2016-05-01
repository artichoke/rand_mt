# Mersenne Twister in Rust

This is a pure rust port of the
[Mersenne Twister](http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/emt.html)
pseudorandom number generators. [See the rustdoc][doc] for suggested usage.

[doc]: https://dcrewi.github.io/rust-mersenne-twister/doc/0.3/mersenne_twister/index.html

## Algorithms

- MT19937 (32-bit version)
- MT19937-64 (64-bit version)

## Stability

This crate takes advantage of rust's built-in benchmarking, which is
still an unstable feature as of 1.8. Until it stabilizes, one must
compile the tests for this crate with nightly, or fork the crate and
remove the benchmarks.
