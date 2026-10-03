# rand_mt

[![GitHub Actions](https://github.com/artichoke/rand_mt/actions/workflows/ci.yaml/badge.svg)](https://github.com/artichoke/rand_mt/actions)
[![Crate](https://img.shields.io/crates/v/rand_mt.svg)](https://crates.io/crates/rand_mt)
[![API](https://docs.rs/rand_mt/badge.svg)](https://docs.rs/rand_mt)

Reference MT19937 (`Mt`) and MT19937-64 (`Mt64`) pseudorandom number generators.
Artichoke uses `Mt` to reproduce Ruby random number sequences.

> A very fast random number generator of period 2<sup>19937</sup>-1. (Makoto
> Matsumoto, 1997).

The Mersenne Twister algorithms are not suitable for cryptographic uses, but are
ubiquitous. See the [Mersenne Twister website]. A variant of Mersenne Twister is
the [default PRNG in Ruby].

[mersenne twister website]:
  http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/emt.html
[default prng in ruby]: https://ruby-doc.org/core-3.1.2/Random.html

This crate optionally depends on [`rand_core`] 0.10 and implements `TryRng` with
an `Infallible` error, which also provides `Rng` through a blanket impl.

[`rand_core`]: https://crates.io/crates/rand_core

## Usage

Add this to your `Cargo.toml`:

```toml
[dependencies]
rand_mt = "6.1.0"
```

Then create a RNG with an explicit seed:

```rust
use rand_mt::Mt64;

let mut rng = Mt64::new(0x0123_4567_89ab_cdef_u64);
assert_ne!(rng.next_u64(), rng.next_u64());
```

`Mt::new_unseeded()` and `Mt64::new_unseeded()` are deterministic shortcuts for
the reference seed. They are intended for reproducible streams and tests and do
not gather entropy.

## Crate Features

`rand_mt` is `no_std` and does not require `alloc`. It has one optional feature,
enabled by default:

- **rand-traits** - Enables a dependency on [`rand_core`]. Activating this
  feature implements `TryRng` and `SeedableRng` on the RNGs in this crate, with
  `Rng` provided by `rand_core`.

Disable the default feature to use the generators without dependencies:

```toml
[dependencies]
rand_mt = { version = "6.1.0", default-features = false }
```

Mersenne Twister requires approximately 2.5 kilobytes of internal state. To make
the RNGs implemented in this crate practical to embed in other structs, you may
wish to store the RNG in a `Box`.

### Minimum Supported Rust Version

This crate requires at least Rust 1.88.0. This version can be bumped in minor
releases. Rust 1.88 enables typed slice chunks for byte filling.

## License

`rand_mt` is distributed under the terms of either the
[MIT License](LICENSE-MIT) or the
[Apache License (Version 2.0)](LICENSE-APACHE).

`rand_mt` is derived from `rust-mersenne-twister` @ [`1.1.1`] which is Copyright
(c) 2015 rust-mersenne-twister developers.

[`1.1.1`]: https://github.com/dcrewi/rust-mersenne-twister/tree/1.1.1
