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

use core::cmp;
use core::fmt;
use core::hash;
use core::num::Wrapping;

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
/// The official name of this RNG is `MT19937`. It natively outputs `u32`.
///
/// # Size
///
/// `Mt19937GenRand32` requires approximately 2.5KB of internal state.
///
/// You may wish to store an `Mt19937GenRand32` on the heap in a `Box` to make
/// it easier to embed in another struct.
///
/// `Mt19937GenRand32` is also the same size as
/// [`Mt19937GenRand64`](crate::Mt19937GenRand64).
///
/// ```
/// # use core::mem;
/// # use rand_mt::{Mt19937GenRand32, Mt19937GenRand64};
/// assert_eq!(2504, mem::size_of::<Mt19937GenRand32>());
/// assert_eq!(mem::size_of::<Mt19937GenRand64>(), mem::size_of::<Mt19937GenRand32>());
/// ```
#[derive(Clone)]
pub struct Mt19937GenRand32 {
    idx: usize,
    state: [Wrapping<u32>; N],
}

impl cmp::Eq for Mt19937GenRand32 {}

impl cmp::PartialEq for Mt19937GenRand32 {
    fn eq(&self, other: &Self) -> bool {
        self.state[..] == other.state[..] && self.idx == other.idx
    }
}

impl cmp::Ord for Mt19937GenRand32 {
    fn cmp(&self, other: &Self) -> cmp::Ordering {
        match self.state[..].cmp(&other.state[..]) {
            cmp::Ordering::Equal => self.idx.cmp(&other.idx),
            ordering => ordering,
        }
    }
}

impl cmp::PartialOrd for Mt19937GenRand32 {
    fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl hash::Hash for Mt19937GenRand32 {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.idx.hash(state);
        self.state.hash(state);
    }
}

impl fmt::Debug for Mt19937GenRand32 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Mt19937GenRand32 {{}}")
    }
}

impl Default for Mt19937GenRand32 {
    /// Return a new `Mt19937GenRand32` with the default seed.
    ///
    /// Equivalent to calling [`Mt19937GenRand32::new_unseeded`].
    #[inline]
    fn default() -> Self {
        Self::new_unseeded()
    }
}

impl SeedableRng for Mt19937GenRand32 {
    type Seed = [u8; 4];

    /// Reseed from a little endian encoded `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_core::{RngCore, SeedableRng};
    /// # use rand_mt::Mt19937GenRand32;
    /// // Default MT seed
    /// let seed = 5489_u32.to_le_bytes();
    /// let mut mt = Mt19937GenRand32::from_seed(seed);
    /// assert_ne!(mt.next_u32(), mt.next_u32());
    /// ```
    #[inline]
    fn from_seed(seed: Self::Seed) -> Self {
        Self::new(u32::from_le_bytes(seed))
    }
}

impl RngCore for Mt19937GenRand32 {
    /// Generate next `u64` output.
    ///
    /// This function is implemented by generating two `u32`s from the RNG and
    /// shifting + masking them into a `u64` output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_core::RngCore;
    /// # use rand_mt::Mt19937GenRand32;
    /// let mut mt = Mt19937GenRand32::new_unseeded();
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
    /// # use rand_mt::Mt19937GenRand32;
    /// let mut mt = Mt19937GenRand32::new_unseeded();
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
    /// # use rand_mt::Mt19937GenRand32;
    /// let mut mt = Mt19937GenRand32::new_unseeded();
    /// let mut buf = [0; 32];
    /// mt.fill_bytes(&mut buf);
    /// assert_ne!([0; 32], buf);
    /// let mut buf = [0; 31];
    /// mt.fill_bytes(&mut buf);
    /// assert_ne!([0; 31], buf);
    /// ```
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut left = dest;
        while left.len() >= 4 {
            let (l, r) = left.split_at_mut(4);
            left = r;
            let chunk: [u8; 4] = self.next_u32().to_le_bytes();
            l.copy_from_slice(&chunk);
        }
        let n = left.len();
        if n > 0 {
            let chunk: [u8; 4] = self.next_u32().to_le_bytes();
            left.copy_from_slice(&chunk[..n]);
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
    /// # use rand_mt::Mt19937GenRand32;
    /// let mut mt = Mt19937GenRand32::new_unseeded();
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

impl Mt19937GenRand32 {
    /// Default seed used by [`Mt19937GenRand32::new_unseeded`].
    pub const DEFAULT_SEED: u32 = 5489_u32;

    /// Create a new Mersenne Twister random number generator using the given
    /// seed.
    ///
    /// # Examples
    ///
    /// ## Constructing with a `u32` seed
    ///
    /// ```
    /// # use rand_core::SeedableRng;
    /// # use rand_mt::Mt19937GenRand32;
    /// let seed = 123_456_789_u32;
    /// let mt1 = Mt19937GenRand32::new(seed);
    /// let mt2 = Mt19937GenRand32::from_seed(seed.to_le_bytes());
    /// assert_eq!(mt1, mt2);
    /// ```
    ///
    /// ## Constructing with default seed
    ///
    /// ```
    /// # use rand_mt::Mt19937GenRand32;
    /// let mt1 = Mt19937GenRand32::new(Mt19937GenRand32::DEFAULT_SEED);
    /// let mt2 = Mt19937GenRand32::new_unseeded();
    /// assert_eq!(mt1, mt2);
    /// ```
    #[inline]
    #[must_use]
    pub fn new(seed: u32) -> Self {
        let mut mt = Self {
            idx: 0,
            state: [Wrapping(0); N],
        };
        mt.reseed(seed);
        mt
    }

    /// Create a new Mersenne Twister random number generator using the given
    /// key.
    #[inline]
    #[must_use]
    pub fn new_from_slice(key: &[u32]) -> Self {
        Self::new_from_iter(key.iter().copied())
    }

    /// Create a new Mersenne Twister random number generator using the given
    /// key.
    #[must_use]
    pub fn new_from_iter<I>(key: I) -> Self
    where
        I: IntoIterator<Item = u32>,
        I::IntoIter: Clone,
    {
        let mut mt = Self {
            idx: 0,
            state: [Wrapping(0); N],
        };
        mt.reseed_from_iter(key);
        mt
    }

    /// Create a new Mersenne Twister random number generator using the default
    /// fixed seed.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_core::SeedableRng;
    /// # use rand_mt::Mt19937GenRand32;
    /// // Default MT seed
    /// let seed = 5489_u32;
    /// let mt = Mt19937GenRand32::new(seed);
    /// let unseeded = Mt19937GenRand32::new_unseeded();
    /// assert_eq!(mt, unseeded);
    /// ```
    #[inline]
    #[must_use]
    pub fn new_unseeded() -> Self {
        Self::new(Self::DEFAULT_SEED)
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
    /// The returned `Mt19937GenRand32` is guaranteed to identically reproduce
    /// subsequent outputs of the RNG that was sampled.
    ///
    /// Returns `None` if `samples` is not exactly 624 elements.
    #[inline]
    #[must_use]
    pub fn recover(samples: &[u32]) -> Option<Self> {
        Self::recover_from_iter(samples.iter().copied())
    }

    /// Recover the internal state of a Mersenne Twister instance
    /// from 624 consecutive outputs of the algorithm.
    ///
    /// The returned `Mt19937GenRand32` is guaranteed to identically reproduce
    /// subsequent outputs of the RNG that was sampled.
    ///
    /// Returns `None` if `samples` is not exactly 624 elements.
    #[must_use]
    pub fn recover_from_iter<I>(samples: I) -> Option<Self>
    where
        I: IntoIterator<Item = u32>,
    {
        let mut mt = Self {
            idx: N,
            state: [Wrapping(0); N],
        };
        let mut state = mt.state.iter_mut();
        for sample in samples {
            let out = state.next()?; // Too many samples
            *out = Wrapping(untemper(sample));
        }
        // If the state iterator still has unfilled cells, the given iterator
        // was too short. If there are no additional cells, return the
        // initialized RNG.
        if state.next().is_none() {
            Some(mt)
        } else {
            None
        }
    }

    /// Reseed a Mersenne Twister from a single `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_core::{RngCore, SeedableRng};
    /// # use rand_mt::Mt19937GenRand32;
    /// // Default MT seed
    /// let mut mt = Mt19937GenRand32::new_unseeded();
    /// let first = mt.next_u32();
    /// mt.fill_bytes(&mut [0; 512]);
    /// // Default MT seed
    /// mt.reseed(5489_u32);
    /// assert_eq!(first, mt.next_u32());
    /// ```
    #[allow(clippy::cast_possible_truncation)]
    pub fn reseed(&mut self, seed: u32) {
        self.idx = N;
        self.state[0] = Wrapping(seed);
        for i in 1..N {
            self.state[i] = Wrapping(1_812_433_253)
                * (self.state[i - 1] ^ (self.state[i - 1] >> 30))
                + Wrapping(i as u32);
        }
    }

    /// Reseed a Mersenne Twister from a slice of `u32`s.
    #[inline]
    pub fn reseed_from_slice(&mut self, key: &[u32]) {
        self.reseed_from_iter(key.iter().copied())
    }

    /// Reseed a Mersenne Twister from am iterator of `u32`s.
    #[allow(clippy::cast_possible_truncation)]
    pub fn reseed_from_iter<I>(&mut self, key: I)
    where
        I: IntoIterator<Item = u32>,
        I::IntoIter: Clone,
    {
        self.reseed(19_650_218_u32);
        let mut i = 1_usize;
        for (j, piece) in key.into_iter().enumerate().cycle().take(N) {
            self.state[i] = (self.state[i]
                ^ ((self.state[i - 1] ^ (self.state[i - 1] >> 30)) * Wrapping(1_664_525)))
                + Wrapping(piece)
                + Wrapping(j as u32);
            i += 1;
            if i >= N {
                self.state[0] = self.state[N - 1];
                i = 1;
            }
        }
        for _ in 0..N - 1 {
            self.state[i] = (self.state[i]
                ^ ((self.state[i - 1] ^ (self.state[i - 1] >> 30)) * Wrapping(1_566_083_941)))
                - Wrapping(i as u32);
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

#[cfg(test)]
mod tests {
    use core::num::Wrapping;
    use quickcheck_macros::quickcheck;
    use rand_core::{RngCore, SeedableRng};

    use super::Mt19937GenRand32;
    use crate::vectors::mt as vectors;

    #[test]
    fn seeded_state_from_u32_seed() {
        let mt = Mt19937GenRand32::new(0x1234_5678_u32);
        let mt_from_seed = Mt19937GenRand32::from_seed(0x1234_5678_u32.to_le_bytes());
        assert!(mt.state[..] == mt_from_seed.state[..]);
        for (&Wrapping(x), &y) in mt.state.iter().zip(vectors::STATE_SEEDED_BY_U32.iter()) {
            assert!(x == y);
        }
    }

    #[test]
    fn seeded_state_from_u32_slice_key() {
        let mt =
            Mt19937GenRand32::new_from_slice(&[0x123_u32, 0x234_u32, 0x345_u32, 0x456_u32][..]);
        for (&Wrapping(x), &y) in mt.state.iter().zip(vectors::STATE_SEEDED_BY_SLICE.iter()) {
            assert!(x == y);
        }
    }

    #[test]
    fn output_from_u32_slice_key() {
        let mut mt =
            Mt19937GenRand32::new_from_slice(&[0x123_u32, 0x234_u32, 0x345_u32, 0x456_u32][..]);
        for x in vectors::TEST_OUTPUT.iter() {
            assert!(mt.next_u32() == *x);
        }
    }

    #[quickcheck]
    fn temper_untemper_is_identity(x: u32) -> bool {
        x == super::untemper(super::temper(x))
    }

    #[quickcheck]
    fn untemper_temper_is_identity(x: u32) -> bool {
        x == super::temper(super::untemper(x))
    }

    #[quickcheck]
    fn recovery(seed: u32, skip: u8) -> bool {
        let mut orig_mt = Mt19937GenRand32::new(seed);
        // skip some samples so the RNG is in an intermediate state
        for _ in 0..skip {
            orig_mt.next_u32();
        }
        let mut samples = [0; 624];
        for sample in samples.iter_mut() {
            *sample = orig_mt.next_u32();
        }
        let mut recovered_mt = Mt19937GenRand32::recover(&samples[..]).unwrap();
        for _ in 0..624 * 2 {
            if orig_mt.next_u32() != recovered_mt.next_u32() {
                return false;
            }
        }
        true
    }

    #[test]
    fn recover_required_exact_sample_length() {
        assert_eq!(None, Mt19937GenRand32::recover(&[0; 0][..]));
        assert_eq!(None, Mt19937GenRand32::recover(&[0; 1][..]));
        assert_eq!(None, Mt19937GenRand32::recover(&[0; 625][..]));
        assert_eq!(None, Mt19937GenRand32::recover(&[0; 1000][..]));
    }
}
