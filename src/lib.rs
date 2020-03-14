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
#![deny(missing_docs, intra_doc_link_resolution_failure)]
#![warn(rust_2018_idioms)]
#![forbid(unsafe_code)]

//! # Mersenne Twister
//!
//! A pure rust port of the Mersenne Twister pseudorandom number
//! generator.
//!
//! **THESE ALGORITHMS ARE NOT APPROPRIATE FOR CRYPTOGRAPHIC USE.**
//! After observing a couple hundred outputs, it is possible to
//! predict all future outputs. This library even implements a
//! `recover` constructor to reconstruct the RNG state from output
//! samples.
//!
//!
//! ## Usage
//!
//! If your application does not require a specific Mersenne Twister
//! flavor (32-bit or 64-bit), you can use the default flavor for your
//! target platform by using the `MersenneTwister` type
//! definition. Either flavor accepts a `u64` seed.
//!
//! ```
//! # use rand_mt::MersenneTwister;
//! # use rand_core::{RngCore, SeedableRng};
//! # fn main() -> Result<(), Box<dyn std::error::Error>> {
//! // Get a seed somehow.
//! let seed: [u8; 8] = 0x1234_567_89ab_cdef_u64.to_ne_bytes();
//! // Create the default RNG.
//! let mut rng = MersenneTwister::from_seed(seed);
//! // start grabbing randomness from rng...
//! let mut buf = vec![0; 512];
//! rng.try_fill_bytes(&mut buf)?;
//! # Ok(())
//! # }
//! ```
//!
//! Or if you want to use the default (fixed) seeds that are specified
//! in the reference implementations:
//!
//! ```
//! # use rand_mt::MersenneTwister;
//! use std::default::Default;
//! let mut rng: MersenneTwister = Default::default();
//! ```
//!
//! ## Portability
//!
//! Note that `MT19937` and `MT19937_64` are **not** identical
//! algorithms, despite their similar names. They produce different
//! output streams from the same seed. You will need to pick a
//! specific flavor of the two algorithms if portable reproducibility
//! is important to you.

#![deny(missing_docs)]

pub use crate::mt19937::MT19937;
pub use crate::mt19937_64::MT19937_64;

mod mt19937;
mod mt19937_64;
#[cfg(test)]
mod vectors;

/// The most platform-appropriate Mersenne Twister flavor.
#[cfg(target_pointer_width = "32")]
pub type MersenneTwister = MT19937;

/// The most platform-appropriate Mersenne Twister flavor.
#[cfg(target_pointer_width = "64")]
pub type MersenneTwister = MT19937_64;
