# rand_mt

[![GitHub Actions](https://github.com/artichoke/rand_mt/workflows/CI/badge.svg)](https://github.com/artichoke/rand_mt/actions)
[![Discord](https://img.shields.io/discord/607683947496734760)](https://discord.gg/QCe2tp2)
[![Twitter](https://img.shields.io/twitter/follow/artichokeruby?label=Follow&style=social)](https://twitter.com/artichokeruby)
<br>
[![Crate](https://img.shields.io/crates/v/rand_mt.svg)](https://crates.io/crates/rand_mt)
[![API](https://docs.rs/rand_mt/badge.svg)](https://docs.rs/rand_mt)
[![API trunk](https://img.shields.io/badge/docs-trunk-blue.svg)](https://artichoke.github.io/rand_mt/rand_mt/)

Implemenents a selection of Mersenne Twister random number generators.

> A very fast random number generator of period 2<sup>19937</sup>-1. (Makoto
> Matsumoto, 1997).

The Mersenne Twister algorithms are not suitable for cryptographic uses, but are
ubiquitous. See the [Mersenne Twister website]. A variant of Mersenne Twister is
the [default PRNG in Ruby].

This crate optionally depends on [rand_core] and implements `RngCore` on the
RNGs in this crate.

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
rand_mt = "4.1.1"
```

Then create a RNG like:

```rust
use rand_mt::Mt64;

let mut rng = Mt64::new_unseeded();
assert_ne!(rng.next_u64(), rng.next_u64());
```

## Crate Features

`rand_mt` is `no_std` compatible. `rand_mt` has several optional features that
are enabled by default:

- **rand-traits** - Enables a dependency on [`rand_core`]. Activating this
  feature implements `RngCore` and `SeedableRng` on the RNGs in this crate.
- **std** - Enables a dependency on the Rust Standard Library. Activating this
  feature enables [`std::error::Error`] impls on error types in this crate.

Mersenne Twister requires ~2.5KB of internal state. To make the RNGs implemented
in this crate practical to embed in other structs, you may wish to store the RNG
in a `Box`.

### Minimum Supported Rust Version

This crate requires at least Rust 1.47.0. This version can be bumped in minor
releases.

## License

`rand_mt` is distributed under the terms of either the
[MIT License](LICENSE-MIT) or the
[Apache License (Version 2.0)](LICENSE-APACHE).

`rand_mt` is derived from `rust-mersenne-twister` @ [`1.1.1`] which is Copyright
(c) 2015 rust-mersenne-twister developers.

[mersenne twister website]:
  http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/emt.html
[default prng in ruby]: https://ruby-doc.org/core-2.6.3/Random.html
[rand_core]: https://crates.io/crates/rand_core
[`rand_core`]: https://crates.io/crates/rand_core
[`std::error::error`]: https://doc.rust-lang.org/std/error/trait.Error.html
[`1.1.1`]: https://github.com/dcrewi/rust-mersenne-twister/tree/1.1.1
