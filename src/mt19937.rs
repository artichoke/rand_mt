// src/mt19937.rs
//
// Copyright (c) 2015,2017 rust-mersenne-twister developers
// Copyright (c) 2020 Ryan Lopopolo <rjl@hyperbo.la>
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

use std::cmp;
use std::convert::TryFrom;
use std::num::Wrapping;

use rand_core::{RngCore, SeedableRng};

const N: usize = 624;
const M: usize = 397;
const ONE: Wrapping<u32> = Wrapping(1);
const MATRIX_A: Wrapping<u32> = Wrapping(0x9908_b0df);
const UPPER_MASK: Wrapping<u32> = Wrapping(0x8000_0000);
const LOWER_MASK: Wrapping<u32> = Wrapping(0x7fff_ffff);

/// The 32-bit flavor of the Mersenne Twister pseudorandom number
/// generator.
///
/// # Size
///
/// `MT19937` requires approximately 2.5KB of internal state.
///
/// `MT19937` stores its state on the heap to ease embedding a Mersenne Twister
/// in another struct. `MT19937` is also the same size as
/// [`MT19937_64`](crate::MT19937_64).
///
/// ```
/// # use rand_mt::{MT19937, MT19937_64};
/// # use std::mem;
/// assert_eq!(3 * mem::size_of::<usize>(), mem::size_of::<MT19937>());
/// assert_eq!(mem::size_of::<MT19937_64>(), mem::size_of::<MT19937>());
/// ```
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct MT19937 {
    idx: usize,
    state: Box<[Wrapping<u32>]>, // Length `N`.
}

impl SeedableRng for MT19937 {
    type Seed = [u8; 4];

    /// Reseed from a little endian encoded `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_core::{RngCore, SeedableRng};
    /// # use rand_mt::MT19937;
    /// // Default MT seed
    /// let seed = 5489_u32.to_le_bytes();
    /// let mut mt = MT19937::from_seed(seed);
    /// assert_ne!(mt.next_u32(), mt.next_u32());
    /// ```
    #[inline]
    fn from_seed(seed: Self::Seed) -> Self {
        let mut mt = Self::uninitialized();
        mt.reseed(u32::from_le_bytes(seed));
        mt
    }
}

impl RngCore for MT19937 {
    /// Generate next `u64` output.
    ///
    /// This function is implemented by generating two `u32`s from the RNG and
    /// shifting + masking them into a `u64` output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_core::RngCore;
    /// # use rand_mt::MT19937;
    /// let mut mt = MT19937::new_unseeded();
    /// assert_ne!(mt.next_u64(), mt.next_u64());
    /// ```
    #[inline]
    fn next_u64(&mut self) -> u64 {
        let out = u64::from(self.next_u32());
        let out = out << 32;
        out | u64::from(self.next_u32())
    }

    /// Generate next `u32` output.
    ///
    /// `u32` is the native output of the generator. This function advances the
    /// RNG step counter by one.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_core::RngCore;
    /// # use rand_mt::MT19937;
    /// let mut mt = MT19937::new_unseeded();
    /// assert_ne!(mt.next_u32(), mt.next_u32());
    /// ```
    #[inline]
    fn next_u32(&mut self) -> u32 {
        // Failing this check indicates that, somehow, the structure
        // was not initialized.
        debug_assert!(self.idx != 0);
        if self.idx >= N {
            self.fill_next_state();
        }
        let Wrapping(x) = self.state[self.idx];
        self.idx += 1;
        temper(x)
    }

    /// Fill a buffer with bytes generated from the RNG.
    ///
    /// This method generates random `u32`s (the native output unit of the RNG)
    /// until `dest` is filled.
    ///
    /// This method may discard some output bits if `dest.len()` is not a
    /// multiple of 4.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_core::RngCore;
    /// # use rand_mt::MT19937;
    /// let mut mt = MT19937::new_unseeded();
    /// let mut buf = [0; 32];
    /// mt.fill_bytes(&mut buf);
    /// assert_ne!([0; 32], buf);
    /// let mut buf = [0; 31];
    /// mt.fill_bytes(&mut buf);
    /// assert_ne!([0; 31], buf);
    /// ```
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut bytes_written = 0;
        loop {
            if bytes_written >= dest.len() {
                break;
            }
            let bytes = self.next_u32().to_le_bytes();
            if let Some(slice) = dest.get_mut(bytes_written..bytes_written + 4) {
                slice.copy_from_slice(&bytes[..]);
                bytes_written += 4;
            } else {
                for byte in bytes.iter().copied() {
                    if let Some(cell) = dest.get_mut(bytes_written) {
                        *cell = byte;
                        bytes_written += 1;
                    } else {
                        break;
                    }
                }
            }
        }
    }

    /// Fill a buffer with bytes generated from the RNG.
    ///
    /// This method generates random `u32`s (the native output unit of the RNG)
    /// until `dest` is filled.
    ///
    /// This method may discard some output bits if `dest.len()` is not a
    /// multiple of 4.
    ///
    /// `try_fill_bytes` is implemented with [`fill_bytes`](RngCore::fill_bytes)
    /// and is infallible.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_core::RngCore;
    /// # use rand_mt::MT19937;
    /// let mut mt = MT19937::new_unseeded();
    /// let mut buf = [0; 32];
    /// mt.try_fill_bytes(&mut buf).unwrap();
    /// assert_ne!([0; 32], buf);
    /// let mut buf = [0; 31];
    /// mt.try_fill_bytes(&mut buf).unwrap();
    /// assert_ne!([0; 31], buf);
    /// ```
    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl MT19937 {
    /// Generate an `MT19937` with zeroed state.
    fn uninitialized() -> Self {
        Self {
            idx: 0,
            state: vec![Wrapping(0); N].into_boxed_slice(),
        }
    }

    /// Create a new Mersenne Twister random number generator using
    /// the default fixed seed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_core::SeedableRng;
    /// # use rand_mt::MT19937;
    /// // Default MT seed
    /// let seed = 5489_u32.to_le_bytes();
    /// let mt = MT19937::from_seed(seed);
    /// let unseeded = MT19937::new_unseeded();
    /// assert_eq!(mt, unseeded);
    /// ```
    #[inline]
    #[must_use]
    pub fn new_unseeded() -> Self {
        Self::from_seed(5489_u32.to_le_bytes())
    }

    fn fill_next_state(&mut self) {
        for i in 0..N - M {
            let x = (self.state[i] & UPPER_MASK) | (self.state[i + 1] & LOWER_MASK);
            self.state[i] = self.state[i + M] ^ (x >> 1) ^ ((x & ONE) * MATRIX_A);
        }
        for i in N - M..N - 1 {
            let x = (self.state[i] & UPPER_MASK) | (self.state[i + 1] & LOWER_MASK);
            self.state[i] = self.state[i + M - N] ^ (x >> 1) ^ ((x & ONE) * MATRIX_A);
        }
        let x = (self.state[N - 1] & UPPER_MASK) | (self.state[0] & LOWER_MASK);
        self.state[N - 1] = self.state[M - 1] ^ (x >> 1) ^ ((x & ONE) * MATRIX_A);
        self.idx = 0;
    }

    /// Recover the internal state of a Mersenne Twister instance
    /// from 624 consecutive outputs of the algorithm.
    ///
    /// The returned `MT19937` is guaranteed to identically reproduce
    /// subsequent outputs of the RNG that was sampled.
    ///
    /// Returns `None` if `samples` is not exactly 624 elements.
    #[must_use]
    pub fn recover(samples: &[u32]) -> Option<Self> {
        if samples.len() != N {
            return None;
        }
        let mut mt = Self::uninitialized();
        for (in_, out) in Iterator::zip(samples.iter().copied(), mt.state.iter_mut()) {
            *out = Wrapping(untemper(in_));
        }
        mt.idx = N;
        Some(mt)
    }

    /// Reseed a Mersenne Twister from a single `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_core::{RngCore, SeedableRng};
    /// # use rand_mt::MT19937;
    /// // Default MT seed
    /// let seed = 5489_u32.to_le_bytes();
    /// let mut mt = MT19937::from_seed(seed);
    /// let first = mt.next_u32();
    /// mt.fill_bytes(&mut [0; 512]);
    /// // Default MT seed
    /// mt.reseed(5489_u32);
    /// assert_eq!(first, mt.next_u32());
    /// ```
    pub fn reseed(&mut self, seed: u32) {
        self.idx = N;
        self.state[0] = Wrapping(seed);
        for i in 1..N {
            self.state[i] = Wrapping(1_812_433_253)
                * (self.state[i - 1] ^ (self.state[i - 1] >> 30))
                + Wrapping(u32::try_from(i).unwrap_or_default());
        }
    }

    /// Reseed a Mersenne Twister from a sequence of `u32`s.
    pub fn reseed_from_slice(&mut self, key: &[u32]) {
        self.reseed(19_650_218_u32);
        let mut i = 1_usize;
        let mut j = 0_usize;
        for _ in 0..cmp::max(N, key.len()) {
            self.state[i] = (self.state[i]
                ^ ((self.state[i - 1] ^ (self.state[i - 1] >> 30)) * Wrapping(1_664_525)))
                + Wrapping(key[j])
                + Wrapping(u32::try_from(j).unwrap_or_default());
            i += 1;
            if i >= N {
                self.state[0] = self.state[N - 1];
                i = 1;
            }
            j += 1;
            if j >= key.len() {
                j = 0;
            }
        }
        for _ in 0..N - 1 {
            self.state[i] = (self.state[i]
                ^ ((self.state[i - 1] ^ (self.state[i - 1] >> 30)) * Wrapping(1_566_083_941)))
                - Wrapping(u32::try_from(i).unwrap_or_default());
            i += 1;
            if i >= N {
                self.state[0] = self.state[N - 1];
                i = 1;
            }
        }
        self.state[0] = Wrapping(1 << 31);
    }
}

#[inline]
fn temper(mut x: u32) -> u32 {
    x ^= x >> 11;
    x ^= (x << 7) & 0x9d2c_5680;
    x ^= (x << 15) & 0xefc6_0000;
    x ^= x >> 18;
    x
}

#[inline]
fn untemper(mut x: u32) -> u32 {
    // reverse "x ^=  x>>18;"
    x ^= x >> 18;

    // reverse "x ^= (x<<15) & 0xefc6_0000;"
    x ^= (x << 15) & 0x2fc6_0000;
    x ^= (x << 15) & 0xc000_0000;

    // reverse "x ^= (x<< 7) & 0x9d2c_5680;"
    x ^= (x << 7) & 0x0000_1680;
    x ^= (x << 7) & 0x000c_4000;
    x ^= (x << 7) & 0x0d20_0000;
    x ^= (x << 7) & 0x9000_0000;

    // reverse "x ^=  x>>11;"
    x ^= x >> 11;
    x ^= x >> 22;

    x
}

impl Default for MT19937 {
    #[inline]
    fn default() -> Self {
        Self::new_unseeded()
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;
    use rand_core::{RngCore, SeedableRng};
    use std::num::Wrapping;

    use super::MT19937;
    use crate::vectors::mt as vectors;

    #[test]
    fn test_32bit_seeded() {
        let mt = MT19937::from_seed(0x1234_5678_u32.to_le_bytes());
        for (&Wrapping(x), &y) in mt.state.iter().zip(vectors::STATE_SEEDED_BY_U32.iter()) {
            assert!(x == y);
        }
    }

    #[test]
    fn test_32bit_slice_seeded() {
        let mut mt = MT19937::default();
        mt.reseed_from_slice(&[0x123_u32, 0x234_u32, 0x345_u32, 0x456_u32][..]);
        for (&Wrapping(x), &y) in mt.state.iter().zip(vectors::STATE_SEEDED_BY_SLICE.iter()) {
            assert!(x == y);
        }
    }

    #[test]
    fn test_32bit_output() {
        let mut mt = MT19937::default();
        mt.reseed_from_slice(&[0x123_u32, 0x234_u32, 0x345_u32, 0x456_u32][..]);
        for x in vectors::TEST_OUTPUT.iter() {
            assert!(mt.next_u32() == *x);
        }
    }

    #[quickcheck]
    fn test_untemper(x: u32) -> bool {
        x == super::untemper(super::temper(x))
    }

    #[quickcheck]
    fn test_recovery(seed: u32, skip: u8) -> bool {
        let mut orig_mt = MT19937::from_seed(seed.to_le_bytes());
        // skip some samples so the RNG is in an intermediate state
        for _ in 0..skip {
            orig_mt.next_u64();
        }
        let mut samples = Vec::with_capacity(super::N);
        for _ in 0..super::N {
            samples.push(orig_mt.next_u32());
        }
        let mut recovered_mt = MT19937::recover(&samples[..]).unwrap();
        for _ in 0..super::N * 2 {
            if orig_mt.next_u32() != recovered_mt.next_u32() {
                return false;
            }
        }
        true
    }
}
