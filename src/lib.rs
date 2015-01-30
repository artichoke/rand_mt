// src/lib.rs
//
// Copyright 2015 David Creswick
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

//! # Mersenne Twister
//!
//! A pure rust port of the Mersenne Twister pseudorandom number
//! generator.
//!
//! **THESE ALGORITHMS ARE NOT APPROPRIATE FOR CRYPTOGRAPHIC USE.**
//!
//!
//! ## Usage
//!
//! If your application does not require a specific Mersenne Twister
//! flavor, you can use the default one for your target platform this
//! way:
//!
//! ```
//! extern crate mersenne_twister;
//! use mersenne_twister::MersenneTwister;
//! use std::rand::{Rng, SeedableRng};
//!
//! fn main() {
//!     // Get a seed somehow.
//!     let seed: u64 = 0x123456789abcdef;
//!     // Create the default RNG.
//!     let mut rng: MersenneTwister = SeedableRng::from_seed(seed);
//!
//!     // start grabbing randomness from rng...
//! }
//! ```
//!
//! Or if you want to use the default (fixed) seeds:
//!
//! ```
//! # use mersenne_twister::MersenneTwister;
//! # use std::rand::{Rng, SeedableRng};
//! use std::default::Default;
//! let mut rng: MersenneTwister = Default::default();
//! ```
//!
//! ## Portability
//!
//! Note that `MT19937` and `MT19937_64` are **not** identical
//! algorithms, despite their similar names. They produce different
//! output streams when given the same seed. You will need to pick a
//! specific flavor of the algorithm if portable reproducibility is
//! important to you.

#![unstable]
#![allow(unstable)]
#![deny(missing_docs)]

#[cfg(test)]
extern crate test;

pub use mt19937::MT19937;
pub use mt19937_64::MT19937_64;

mod mt19937;
mod mt19937_64;


/// The most platform-appropriate Mersenne Twister flavor.
#[cfg(target_pointer_width = "32")]
pub type MersenneTwister = MT19937;

/// The most platform-appropriate Mersenne Twister flavor.
#[cfg(target_pointer_width = "64")]
pub type MersenneTwister = MT19937_64;
