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

use core::convert::TryFrom;
use core::fmt;
use core::mem::size_of;
use core::num::Wrapping;

use crate::RecoverRngError;

#[cfg(feature = "rand-traits")]
mod rand;

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
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
#[allow(clippy::module_name_repetitions)]
pub struct Mt19937GenRand32 {
    idx: usize,
    state: [Wrapping<u32>; N],
}

impl fmt::Debug for Mt19937GenRand32 {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Mt19937GenRand64 {}")
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

impl From<[u8; 4]> for Mt19937GenRand32 {
    /// Construct a Mersenne Twister RNG from 4 bytes.
    ///
    /// The given bytes are treated as a little endian encoded `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_mt::Mt19937GenRand32;
    /// // Default MT seed
    /// let seed = 5489_u32.to_le_bytes();
    /// let mut mt = Mt19937GenRand32::from(seed);
    /// assert_ne!(mt.next_u32(), mt.next_u32());
    /// ```
    ///
    /// This constructor is equivalent to passing a little endian encoded `u32`.
    ///
    /// ```
    /// # use rand_mt::Mt19937GenRand32;
    /// // Default MT seed
    /// let seed = 5489_u32.to_le_bytes();
    /// let mt1 = Mt19937GenRand32::from(seed);
    /// let mt2 = Mt19937GenRand32::new(5489_u32);
    /// assert_eq!(mt1, mt2);
    /// ```
    #[inline]
    fn from(seed: [u8; 4]) -> Self {
        Self::new(u32::from_le_bytes(seed))
    }
}

impl From<u32> for Mt19937GenRand32 {
    /// Construct a Mersenne Twister RNG from a `u32` seed.
    ///
    /// This function is equivalent to [`new`].
    ///
    /// [`new`]: Self::new
    #[inline]
    fn from(seed: u32) -> Self {
        Self::new(seed)
    }
}

impl From<[u32; N]> for Mt19937GenRand32 {
    /// Recover the internal state of a Mersenne Twister using the past 624
    /// samples.
    ///
    /// This conversion takes a history of samples from a RNG and returns a
    /// RNG that will produce identical output to the RNG that supplied the
    /// samples.
    #[inline]
    fn from(key: [u32; N]) -> Self {
        let mut mt = Self {
            idx: N,
            state: [Wrapping(0); N],
        };
        for (sample, out) in key.iter().copied().zip(mt.state.iter_mut()) {
            *out = Wrapping(untemper(sample));
        }
        mt
    }
}

impl TryFrom<&[u32]> for Mt19937GenRand32 {
    type Error = RecoverRngError;

    /// Attempt to recover the internal state of a Mersenne Twister using the
    /// past 624 samples.
    ///
    /// This conversion takes a history of samples from a RNG and returns a
    /// RNG that will produce identical output to the RNG that supplied the
    /// samples.
    ///
    /// This conversion is implemented with [`Mt19937GenRand32::recover`].
    ///
    /// # Errors
    ///
    /// If `key` has less than 624 elements, an error is returned because there
    /// is not enough data to fully initialize the RNG.
    ///
    /// If `key` has more than 624 elements, an error is returned because the
    /// recovered RNG will not produce identical output to the RNG that supplied
    /// the samples.
    #[inline]
    fn try_from(key: &[u32]) -> Result<Self, Self::Error> {
        Self::recover(key.iter().copied())
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
    /// # use rand_mt::Mt19937GenRand32;
    /// let seed = 123_456_789_u32;
    /// let mt1 = Mt19937GenRand32::new(seed);
    /// let mt2 = Mt19937GenRand32::from(seed.to_le_bytes());
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
    ///
    /// Key can have any length.
    #[inline]
    #[must_use]
    pub fn new_with_key<I>(key: I) -> Self
    where
        I: IntoIterator<Item = u32>,
        I::IntoIter: Clone,
    {
        let mut mt = Self {
            idx: 0,
            state: [Wrapping(0); N],
        };
        mt.reseed_with_key(key);
        mt
    }

    /// Create a new Mersenne Twister random number generator using the default
    /// fixed seed.
    ///
    /// # Examples
    ///
    /// ```
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

    /// Generate next `u64` output.
    ///
    /// This function is implemented by generating two `u32`s from the RNG and
    /// shifting + masking them into a `u64` output.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_mt::Mt19937GenRand32;
    /// let mut mt = Mt19937GenRand32::new_unseeded();
    /// assert_ne!(mt.next_u64(), mt.next_u64());
    /// ```
    #[inline]
    pub fn next_u64(&mut self) -> u64 {
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
    /// # use rand_mt::Mt19937GenRand32;
    /// let mut mt = Mt19937GenRand32::new_unseeded();
    /// assert_ne!(mt.next_u32(), mt.next_u32());
    /// ```
    #[inline]
    pub fn next_u32(&mut self) -> u32 {
        // Failing this check indicates that, somehow, the structure
        // was not initialized.
        debug_assert!(self.idx != 0);
        if self.idx >= N {
            fill_next_state(self);
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
    /// # use rand_mt::Mt19937GenRand32;
    /// let mut mt = Mt19937GenRand32::new_unseeded();
    /// let mut buf = [0; 32];
    /// mt.fill_bytes(&mut buf);
    /// assert_ne!([0; 32], buf);
    /// let mut buf = [0; 31];
    /// mt.fill_bytes(&mut buf);
    /// assert_ne!([0; 31], buf);
    /// ```
    #[inline]
    pub fn fill_bytes(&mut self, dest: &mut [u8]) {
        const CHUNK: usize = size_of::<u32>();
        let mut dest_chunks = dest.chunks_exact_mut(CHUNK);

        for next in &mut dest_chunks {
            let chunk: [u8; CHUNK] = self.next_u32().to_le_bytes();
            next.copy_from_slice(&chunk);
        }

        dest_chunks
            .into_remainder()
            .iter_mut()
            .zip(self.next_u32().to_le_bytes().iter())
            .for_each(|(cell, &byte)| {
                *cell = byte;
            });
    }

    /// Attempt to recover the internal state of a Mersenne Twister using the
    /// past 624 samples.
    ///
    /// This conversion takes a history of samples from a RNG and returns a
    /// RNG that will produce identical output to the RNG that supplied the
    /// samples.
    ///
    /// This constructor is also available as a [`TryFrom`] implementation for
    /// `&[u32]`.
    ///
    /// # Errors
    ///
    /// If `key` has less than 624 elements, an error is returned because there
    /// is not enough data to fully initialize the RNG.
    ///
    /// If `key` has more than 624 elements, an error is returned because the
    /// recovered RNG will not produce identical output to the RNG that supplied
    /// the samples.
    #[inline]
    pub fn recover<I>(key: I) -> Result<Self, RecoverRngError>
    where
        I: IntoIterator<Item = u32>,
    {
        let mut mt = Self {
            idx: N,
            state: [Wrapping(0); N],
        };
        let mut state = mt.state.iter_mut();
        for sample in key {
            let out = state.next().ok_or(RecoverRngError::TooManySamples(N))?;
            *out = Wrapping(untemper(sample));
        }
        // If the state iterator still has unfilled cells, the given iterator
        // was too short. If there are no additional cells, return the
        // initialized RNG.
        if state.next().is_none() {
            Ok(mt)
        } else {
            Err(RecoverRngError::TooFewSamples(N))
        }
    }

    /// Reseed a Mersenne Twister from a single `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_mt::Mt19937GenRand32;
    /// // Default MT seed
    /// let mut mt = Mt19937GenRand32::new_unseeded();
    /// let first = mt.next_u32();
    /// mt.fill_bytes(&mut [0; 512]);
    /// // Default MT seed
    /// mt.reseed(5489_u32);
    /// assert_eq!(first, mt.next_u32());
    /// ```
    #[inline]
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

    /// Reseed a Mersenne Twister from am iterator of `u32`s.
    ///
    /// Key can have any length.
    #[inline]
    #[allow(clippy::cast_possible_truncation)]
    pub fn reseed_with_key<I>(&mut self, key: I)
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

#[inline]
fn fill_next_state(rng: &mut Mt19937GenRand32) {
    for i in 0..N - M {
        let x = (rng.state[i] & UPPER_MASK) | (rng.state[i + 1] & LOWER_MASK);
        rng.state[i] = rng.state[i + M] ^ (x >> 1) ^ ((x & ONE) * MATRIX_A);
    }
    for i in N - M..N - 1 {
        let x = (rng.state[i] & UPPER_MASK) | (rng.state[i + 1] & LOWER_MASK);
        rng.state[i] = rng.state[i + M - N] ^ (x >> 1) ^ ((x & ONE) * MATRIX_A);
    }
    let x = (rng.state[N - 1] & UPPER_MASK) | (rng.state[0] & LOWER_MASK);
    rng.state[N - 1] = rng.state[M - 1] ^ (x >> 1) ^ ((x & ONE) * MATRIX_A);
    rng.idx = 0;
}

#[cfg(test)]
mod tests {
    use core::convert::TryFrom;
    use core::iter;
    use core::num::Wrapping;

    use super::{Mt19937GenRand32, N};
    use crate::vectors::mt::{STATE_SEEDED_BY_SLICE, STATE_SEEDED_BY_U32, TEST_OUTPUT};
    use crate::RecoverRngError;

    #[test]
    fn seeded_state_from_u32_seed() {
        let mt = Mt19937GenRand32::new(0x1234_5678_u32);
        let mt_from_seed = Mt19937GenRand32::from(0x1234_5678_u32.to_le_bytes());
        assert_eq!(mt.state, mt_from_seed.state);
        for (&Wrapping(x), &y) in mt.state.iter().zip(STATE_SEEDED_BY_U32.iter()) {
            assert_eq!(x, y);
        }
        for (&Wrapping(x), &y) in mt_from_seed.state.iter().zip(STATE_SEEDED_BY_U32.iter()) {
            assert_eq!(x, y);
        }
    }

    #[test]
    fn seeded_state_from_u32_slice_key() {
        let key = [0x123_u32, 0x234_u32, 0x345_u32, 0x456_u32];
        let mt = Mt19937GenRand32::new_with_key(key.iter().copied());
        for (&Wrapping(x), &y) in mt.state.iter().zip(STATE_SEEDED_BY_SLICE.iter()) {
            assert_eq!(x, y);
        }
    }

    #[test]
    fn seed_with_empty_iter_returns() {
        let _ = Mt19937GenRand32::new_with_key(iter::empty());
    }

    #[test]
    fn output_from_u32_slice_key() {
        let key = [0x123_u32, 0x234_u32, 0x345_u32, 0x456_u32];
        let mut mt = Mt19937GenRand32::new_with_key(key.iter().copied());
        for &x in TEST_OUTPUT.iter() {
            assert_eq!(x, mt.next_u32());
        }
    }

    #[test]
    fn temper_untemper_is_identity() {
        let mut buf = [0; 4];
        for _ in 0..10_000 {
            getrandom::getrandom(&mut buf).unwrap();
            let x = u32::from_le_bytes(buf);
            assert_eq!(x, super::untemper(super::temper(x)));
            let x = u32::from_be_bytes(buf);
            assert_eq!(x, super::untemper(super::temper(x)));
        }
    }

    #[test]
    fn untemper_temper_is_identity() {
        let mut buf = [0; 4];
        for _ in 0..10_000 {
            getrandom::getrandom(&mut buf).unwrap();
            let x = u32::from_le_bytes(buf);
            assert_eq!(x, super::temper(super::untemper(x)));
            let x = u32::from_be_bytes(buf);
            assert_eq!(x, super::temper(super::untemper(x)));
        }
    }

    #[test]
    fn recovery_via_from() {
        let mut buf = [0; 4];
        for _ in 0..100 {
            getrandom::getrandom(&mut buf).unwrap();
            let seed = u32::from_le_bytes(buf);
            for skip in 0..256 {
                let mut orig_mt = Mt19937GenRand32::new(seed);
                // skip some samples so the RNG is in an intermediate state
                for _ in 0..skip {
                    orig_mt.next_u32();
                }
                let mut samples = [0; 624];
                for sample in samples.iter_mut() {
                    *sample = orig_mt.next_u32();
                }
                let mut recovered_mt = Mt19937GenRand32::from(samples);
                for _ in 0..624 * 2 {
                    assert_eq!(orig_mt.next_u32(), recovered_mt.next_u32());
                }
            }
        }
    }

    #[test]
    fn recovery_via_recover() {
        let mut buf = [0; 4];
        for _ in 0..100 {
            getrandom::getrandom(&mut buf).unwrap();
            let seed = u32::from_le_bytes(buf);
            for skip in 0..256 {
                let mut orig_mt = Mt19937GenRand32::new(seed);
                // skip some samples so the RNG is in an intermediate state
                for _ in 0..skip {
                    orig_mt.next_u32();
                }
                let mut samples = [0; 624];
                for sample in samples.iter_mut() {
                    *sample = orig_mt.next_u32();
                }
                let mut recovered_mt = Mt19937GenRand32::recover(samples.iter().copied()).unwrap();
                for _ in 0..624 * 2 {
                    assert_eq!(orig_mt.next_u32(), recovered_mt.next_u32());
                }
            }
        }
    }

    #[test]
    fn recover_required_exact_sample_length_via_from() {
        assert_eq!(
            Mt19937GenRand32::try_from(&[0; 0][..]),
            Err(RecoverRngError::TooFewSamples(N))
        );
        assert_eq!(
            Mt19937GenRand32::try_from(&[0; 1][..]),
            Err(RecoverRngError::TooFewSamples(N))
        );
        assert_eq!(
            Mt19937GenRand32::try_from(&[0; 623][..]),
            Err(RecoverRngError::TooFewSamples(N))
        );
        assert!(Mt19937GenRand32::try_from(&[0; 624][..]).is_ok());
        assert_eq!(
            Mt19937GenRand32::try_from(&[0; 625][..]),
            Err(RecoverRngError::TooManySamples(N))
        );
        assert_eq!(
            Mt19937GenRand32::try_from(&[0; 1000][..]),
            Err(RecoverRngError::TooManySamples(N))
        );
    }

    #[test]
    fn recover_required_exact_sample_length_via_recover() {
        assert_eq!(
            Mt19937GenRand32::recover([0; 0].iter().copied()),
            Err(RecoverRngError::TooFewSamples(N))
        );
        assert_eq!(
            Mt19937GenRand32::recover([0; 1].iter().copied()),
            Err(RecoverRngError::TooFewSamples(N))
        );
        assert_eq!(
            Mt19937GenRand32::recover([0; 623].iter().copied()),
            Err(RecoverRngError::TooFewSamples(N))
        );
        assert!(Mt19937GenRand32::recover([0; 624].iter().copied()).is_ok());
        assert_eq!(
            Mt19937GenRand32::recover([0; 625].iter().copied()),
            Err(RecoverRngError::TooManySamples(N))
        );
        assert_eq!(
            Mt19937GenRand32::recover([0; 1000].iter().copied()),
            Err(RecoverRngError::TooManySamples(N))
        );
    }
}
