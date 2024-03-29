// src/lib.rs
//
// Copyright (c) 2015,2017 rust-mersenne-twister developers
// Copyright (c) 2020 Ryan Lopopolo <rjl@hyperbo.la>
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE> or <http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT> or <http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

#![deny(clippy::all)]
#![deny(clippy::pedantic)]
#![deny(clippy::cargo)]
#![allow(unknown_lints)]
#![deny(missing_debug_implementations)]
#![warn(missing_docs)]
#![warn(rust_2018_idioms)]
#![warn(trivial_casts, trivial_numeric_casts)]
#![warn(unused_qualifications)]
#![warn(variant_size_differences)]
#![forbid(unsafe_code)]
// Enable feature callouts in generated documentation:
// https://doc.rust-lang.org/beta/unstable-book/language-features/doc-cfg.html
//
// This approach is borrowed from tokio.
#![cfg_attr(docsrs, feature(doc_cfg))]
#![cfg_attr(docsrs, feature(doc_alias))]

//! Mersenne Twister random number generators.
//!
//! This is a native Rust implementation of a selection of Mersenne Twister
//! generators. Mersenne Twister is not suitable for cryptographic use.
//!
//! This crate provides:
//!
//! - [`Mt19937GenRand32`], the original reference Mersenne Twister
//!   implementation known as `MT19937`. This is a good choice on both 32-bit
//!   and 64-bit CPUs (for 32-bit output).
//! - [`Mt19937GenRand64`], the 64-bit variant of `MT19937` known as
//!   `MT19937-64`. This algorithm produces a different output stream than
//!   `MT19937` and produces 64-bit output. This is a good choice on 64-bit
//!   CPUs.
//!
//! Both of these RNGs use approximately 2.5 kilobytes of state.
//! [`Mt19937GenRand32`] uses a 32-bit seed. [`Mt19937GenRand64`] uses a 64-bit
//! seed. Both can be seeded from an iterator of seeds.
//!
//! Both RNGs implement a `recover` constructor which can reconstruct the RNG
//! state from a sequence of output samples.
//!
//! # Usage
//!
//! You can seed a RNG and begin sampling it:
//!
//! ```
//! # use rand_mt::Mt64;
//! // Create the RNG.
//! let mut rng = Mt64::new(0x1234_567_89ab_cdef_u64);
//! // start grabbing randomness from rng...
//! let mut buf = vec![0; 512];
//! rng.fill_bytes(&mut buf);
//! ```
//!
//! Or if you want to use the default (fixed) seeds that are specified in the
//! reference implementations:
//!
//! ```
//! # use rand_mt::Mt;
//! let default = Mt::default();
//! let mt = Mt::new_unseeded();
//! assert_eq!(default, mt);
//! ```
//!
//! # Crate Features
//!
//! `rand_mt` is `no_std` compatible. `rand_mt` has several optional features
//! that are enabled by default:
//!
//! - **rand-traits** - Enables a dependency on [`rand_core`]. Activating this
//!   feature implements `RngCore` and `SeedableRng` on the RNGs in this crate.
//! - **std** - Enables a dependency on the Rust Standard Library. Activating
//!   this feature enables [`std::error::Error`] impls on error types in this
//!   crate.
//!
//! Mersenne Twister requires approximately 2.5 kilobytes of internal state. To
//! make the RNGs implemented in this crate practical to embed in other structs,
//! you may wish to store the RNG in a [`Box`].
//!
#![cfg_attr(
    not(feature = "std"),
    doc = "[`std::error::Error`]: https://doc.rust-lang.org/std/error/trait.Error.html"
)]
#![cfg_attr(feature = "std", doc = "[`Box`]: std::boxed::Box")]
#![cfg_attr(
    not(feature = "std"),
    doc = "[`Box`]: https://doc.rust-lang.org/std/boxed/struct.Box.html"
)]
#![cfg_attr(
    not(feature = "rand_core"),
    doc = "[`rand_core`]: https://crates.io/crates/rand_core"
)]
//!

#![doc(html_root_url = "https://docs.rs/rand_mt/4.2.2")]
#![no_std]

#[cfg(feature = "std")]
extern crate std;

use core::fmt;

pub use crate::mt::Mt19937GenRand32;
pub use crate::mt64::Mt19937GenRand64;

mod mt;
mod mt64;
#[cfg(test)]
mod vectors;

/// A type alias for [`Mt19937GenRand32`], 32-bit Mersenne Twister.
pub type Mt = Mt19937GenRand32;

/// A type alias for [`Mt19937GenRand64`], 64-bit Mersenne Twister.
pub type Mt64 = Mt19937GenRand64;

/// Error returned from fallible Mersenne Twister recovery constructors.
///
/// When the `std` feature is enabled, this type implements `std::error::Error`.
#[non_exhaustive]
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub enum RecoverRngError {
    /// Attempted to recover an RNG with too many samples.
    ///
    /// Recover constructors require an exact number of samples to ensure the
    /// recovered RNG matches the state of the RNG that supplied all of the
    /// samples.
    TooFewSamples(usize),
    /// Attempted to recover an RNG with too few samples.
    ///
    /// Too few samples leaves the internal state buffer partially
    /// uninitialized.
    ///
    /// Recover constructors require an exact number of samples to ensure the
    /// recovered RNG matches the state of the RNG that supplied all of the
    /// samples.
    TooManySamples(usize),
}

impl fmt::Display for RecoverRngError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::TooFewSamples(expected) => {
                write!(f, "Too few samples given to recover: expected {}", expected)
            }
            Self::TooManySamples(expected) => write!(
                f,
                "Too many samples given to recover: expected {}",
                expected
            ),
        }
    }
}

#[cfg(feature = "std")]
impl std::error::Error for RecoverRngError {}

#[cfg(test)]
mod tests {
    #[cfg(feature = "std")]
    use super::RecoverRngError;

    #[test]
    #[cfg(feature = "std")]
    fn error_display_is_not_empty() {
        use core::fmt::Write as _;
        use std::string::String;

        let test_cases = [
            RecoverRngError::TooFewSamples(0),
            RecoverRngError::TooFewSamples(124),
            RecoverRngError::TooManySamples(0),
            RecoverRngError::TooManySamples(987),
        ];
        for tc in test_cases {
            let mut buf = String::new();
            write!(&mut buf, "{}", tc).unwrap();
            assert!(!buf.is_empty());
        }
    }
}

// Ensure code blocks in `README.md` compile.
//
// This module and macro declaration should be kept at the end of the file, in
// order to not interfere with code coverage.
#[cfg(doctest)]
macro_rules! readme {
    ($x:expr) => {
        #[doc = $x]
        mod readme {}
    };
    () => {
        readme!(include_str!("../README.md"));
    };
}
#[cfg(doctest)]
readme!();
