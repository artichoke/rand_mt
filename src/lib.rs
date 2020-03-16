// src/lib.rs
//
// Copyright (c) 2015,2017 rust-mersenne-twister developers
// Copyright (c) 2020 Ryan Lopopolo <rjl@hyperbo.la>
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

#![deny(clippy::all)]
#![deny(clippy::pedantic)]
#![deny(clippy::cargo)]
#![deny(missing_docs, intra_doc_link_resolution_failure)]
#![deny(missing_debug_implementations)]
#![warn(rust_2018_idioms)]
#![forbid(unsafe_code)]
#![no_std]

//! Mersenne Twister random number generators.
//!
//! This is a native Rust implementation of a selection of Mersenne Twister
//! generators. Mersenne Twister is not suitable for cryptographic use.
//!
//! This crate provides:
//!
//! - [`MT19937`], the original reference Mersenne Twister implementation. This
//!   is a good choice on both 32-bit and 64-bit CPUs (for 32-bit output).
//! - [`MT19937_64`], the 64-bit variant of `MT19937`. This algorithm produces a
//!   different output stream than `MT19937`. This is a good choice on 64-bit
//!   CPUs.
//!
//! Both of these use 2.5KB of state. [`MT19937`] uses a 32-bit seed and can be
//! seeded from a `&[u32]`. [`MT19937_64`] uses a 64-bit seed and can be seeded
//! from a `&[u64]`.
//!
//! Both RNGs implement a `recover` constructor which can reconstruct the RNG
//! state from a sequence of output samples.
//!
//!
//! ## Usage
//!
//! If your application does not require a specific Mersenne Twister flavor
//! (32-bit or 64-bit), you can use the default flavor for your target platform
//! by using the `MersenneTwister` type definition. Either flavor accepts a
//! `u64` seed.
//!
//! ```
//! # use rand_mt::MersenneTwister;
//! # use rand_core::{RngCore, SeedableRng};
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! // Get a seed somehow, expected to be a little endian encoded `u64`.
//! let seed: [u8; 8] = 0x1234_567_89ab_cdef_u64.to_le_bytes();
//! // Create the default RNG.
//! let mut rng = MersenneTwister::from_seed(seed);
//! // start grabbing randomness from rng...
//! let mut buf = vec![0; 512];
//! rng.try_fill_bytes(&mut buf)?;
//! # Ok(())
//! # }
//! ```
//!
//! Or if you want to use the default (fixed) seeds that are specified in the
//! reference implementations:
//!
//! ```
//! # use rand_mt::MersenneTwister;
//! let default = MersenneTwister::default();
//! let mt = MersenneTwister::new_unseeded();
//! assert_eq!(default, mt);
//! ```
//!
//! ## Portability
//!
//! Note that [`MT19937`] and [`MT19937_64`] are **not** identical algorithms,
//! despite their similar names. They produce different output streams from the
//! same seed. You will need to pick a specific flavor of the two algorithms if
//! portable reproducibility is important to you.

pub use crate::mt19937::MT19937;
pub use crate::mt19937_64::MT19937_64;

mod mt19937;
mod mt19937_64;
#[cfg(test)]
mod vectors;

/// The most platform-appropriate Mersenne Twister flavor.
///
/// On 32-bit platforms, this is a type alias to [`MT19937`]. On 64-bit
/// platforms this is a type alias to [`MT19937_64`].
#[cfg(target_pointer_width = "32")]
pub type MersenneTwister = MT19937;

/// The most platform-appropriate Mersenne Twister flavor.
///
/// On 32-bit platforms, this is a type alias to [`MT19937`]. On 64-bit
/// platforms this is a type alias to [`MT19937_64`].
#[cfg(target_pointer_width = "64")]
pub type MersenneTwister = MT19937_64;
