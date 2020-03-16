# rand_mt

[![GitHub Actions](https://github.com/artichoke/rand_mt/workflows/CI/badge.svg)](https://github.com/artichoke/rand_mt/actions)
[![Discord](https://img.shields.io/discord/607683947496734760)](https://discord.gg/QCe2tp2)
[![Twitter](https://img.shields.io/twitter/follow/artichokeruby?label=Follow&style=social)](https://twitter.com/artichokeruby)
<br>
[![Crate](https://img.shields.io/crates/v/rand_mt.svg)](https://crates.io/crates/rand_mt)
[![API](https://docs.rs/rand_mt/badge.svg)](https://docs.rs/rand_mt)
[![API master](https://img.shields.io/badge/docs-master-blue.svg)](https://artichoke.github.io/rand_mt/rand_mt/)

Implemenents a selection of Mersenne Twister random number generators.

> A very fast random number generator of period 2<sup>19937</sup>-1. (Makoto
> Matsumoto, 1997).

The Mersenne Twister algorithms are not suitable for cryptographic uses, but are
ubiquitous. See the
[Mersenne Twister website](http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/emt.html).
A variant of Mersenne Twister is the
[default PRNG in Ruby](https://ruby-doc.org/core-2.6.3/Random.html).

This crate depends on [rand_core](https://crates.io/crates/rand_core).

## Crate Features

`rand_mt` is `no_std` compatible.

Mersenne Twister requires ~2.5KB of internal state. To make the RNGs implemented
in this crate practical to embed in other structs, you may wish to store the RNG
in a `Box`.

## License

`rand_mt` is distributed under the terms of either the
[MIT License](/LICENSE-MIT) or the
[Apache License (Version 2.0)](/LICENSE-APACHE).

`rand_mt` is derived from `rust-mersenne-twister` @
[`1.1.1`](https://github.com/dcrewi/rust-mersenne-twister/tree/1.1.1) which is
Copyright (c) 2015 rust-mersenne-twister developers.
