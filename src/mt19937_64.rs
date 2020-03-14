// src/mt19937_64.rs
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
use std::num::Wrapping;

use rand_core::{RngCore, SeedableRng};

const NN: usize = 312;
const MM: usize = 156;
const ONE: Wrapping<u64> = Wrapping(1);
const MATRIX_A: Wrapping<u64> = Wrapping(0xb502_6f5a_a966_19e9);
const UM: Wrapping<u64> = Wrapping(0xffff_ffff_8000_0000); // Most significant 33 bits
const LM: Wrapping<u64> = Wrapping(0x7fff_ffff); // Least significant 31 bits

/// The 64-bit flavor of the Mersenne Twister pseudorandom number
/// generator.
#[allow(non_camel_case_types)]
#[derive(Debug, Clone, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct MT19937_64 {
    idx: usize,
    state: Box<[Wrapping<u64>]>, // Length `NN`
}

impl SeedableRng for MT19937_64 {
    type Seed = [u8; 8];

    #[inline]
    fn from_seed(seed: Self::Seed) -> Self {
        let mut mt = Self::uninitialized();
        mt.reseed(seed);
        mt
    }
}

impl RngCore for MT19937_64 {
    #[inline]
    fn next_u32(&mut self) -> u32 {
        self.next_u64() as u32
    }

    #[inline]
    fn next_u64(&mut self) -> u64 {
        // Failing this check indicates that, somehow, the structure
        // was not initialized.
        debug_assert!(self.idx != 0);
        if self.idx >= NN {
            self.fill_next_state();
        }
        let Wrapping(x) = self.state[self.idx];
        self.idx += 1;
        temper(x)
    }

    fn fill_bytes(&mut self, dest: &mut [u8]) {
        let mut bytes_written = 0;
        loop {
            if bytes_written >= dest.len() {
                break;
            }
            let bytes = self.next_u64().to_ne_bytes();
            if let Some(slice) = dest.get_mut(bytes_written..bytes_written + 8) {
                slice.copy_from_slice(&bytes[..]);
                bytes_written += 8;
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

    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), rand_core::Error> {
        self.fill_bytes(dest);
        Ok(())
    }
}

impl MT19937_64 {
    fn uninitialized() -> Self {
        Self {
            idx: 0,
            state: vec![Wrapping(0); NN].into_boxed_slice(),
        }
    }

    /// Create a new Mersenne Twister random number generator using
    /// the default fixed seed.
    #[inline]
    pub fn new_unseeded() -> Self {
        Self::from_seed(5489_u64.to_ne_bytes())
    }

    fn fill_next_state(&mut self) {
        for i in 0..NN - MM {
            let x = (self.state[i] & UM) | (self.state[i + 1] & LM);
            self.state[i] = self.state[i + MM] ^ (x >> 1) ^ ((x & ONE) * MATRIX_A);
        }
        for i in NN - MM..NN - 1 {
            let x = (self.state[i] & UM) | (self.state[i + 1] & LM);
            self.state[i] = self.state[i + MM - NN] ^ (x >> 1) ^ ((x & ONE) * MATRIX_A);
        }
        let x = (self.state[NN - 1] & UM) | (self.state[0] & LM);
        self.state[NN - 1] = self.state[MM - 1] ^ (x >> 1) ^ ((x & ONE) * MATRIX_A);
        self.idx = 0;
    }

    /// Recover the internal state of a Mersenne Twister instance
    /// from 312 consecutive outputs of the algorithm.
    ///
    /// The returned `MT19937_64` is guaranteed to identically
    /// reproduce subsequent outputs of the RNG that was sampled.
    ///
    /// Returns `None` if `samples` is not exactly 312 elements.
    pub fn recover(samples: &[<Self as SeedableRng>::Seed]) -> Option<Self> {
        if samples.len() != NN {
            return None;
        }
        let mut mt = Self::uninitialized();
        for (in_, out) in Iterator::zip(samples.iter().copied(), mt.state.iter_mut()) {
            *out = Wrapping(untemper(u64::from_ne_bytes(in_)));
        }
        mt.idx = NN;
        Some(mt)
    }

    /// Reseed a Mersenne Twister from a single `u64`.
    pub fn reseed(&mut self, seed: <Self as SeedableRng>::Seed) {
        self.idx = NN;
        self.state[0] = Wrapping(u64::from_ne_bytes(seed));
        for i in 1..NN {
            self.state[i] = Wrapping(6_364_136_223_846_793_005)
                * (self.state[i - 1] ^ (self.state[i - 1] >> 62))
                + Wrapping(i as u64);
        }
    }

    /// Reseed a Mersenne Twister from a sequence of `u64`s.
    ///
    /// This method can be used to reconstruct a PRNG's internal state from an
    /// observed sequence of random numbers.
    pub fn reseed_from_slice(&mut self, key: &[<Self as SeedableRng>::Seed]) {
        self.reseed(19_650_218_u64.to_ne_bytes());
        let mut i = 1;
        let mut j = 0;
        for _ in 0..cmp::max(NN, key.len()) {
            self.state[i] = (self.state[i]
                ^ ((self.state[i - 1] ^ (self.state[i - 1] >> 62))
                    * Wrapping(3_935_559_000_370_003_845)))
                + Wrapping(u64::from_ne_bytes(key[j]))
                + Wrapping(j as u64);
            i += 1;
            if i >= NN {
                self.state[0] = self.state[NN - 1];
                i = 1;
            }
            j += 1;
            if j >= key.len() {
                j = 0;
            }
        }
        for _ in 0..NN - 1 {
            self.state[i] = (self.state[i]
                ^ ((self.state[i - 1] ^ (self.state[i - 1] >> 62))
                    * Wrapping(2_862_933_555_777_941_757)))
                - Wrapping(i as u64);
            i += 1;
            if i >= NN {
                self.state[0] = self.state[NN - 1];
                i = 1;
            }
        }
        self.state[0] = Wrapping(1 << 63);
    }
}

#[inline]
fn temper(mut x: u64) -> u64 {
    x ^= (x >> 29) & 0x5555_5555_5555_5555;
    x ^= (x << 17) & 0x71d6_7fff_eda6_0000;
    x ^= (x << 37) & 0xfff7_eee0_0000_0000;
    x ^= x >> 43;
    x
}

#[inline]
fn untemper(mut x: u64) -> u64 {
    // reverse "x ^=  x >> 43;"
    x ^= x >> 43;

    // reverse "x ^= (x << 37) & 0xfff7_eee0_0000_0000;"
    x ^= (x << 37) & 0xfff7_eee0_0000_0000;

    // reverse "x ^= (x << 17) & 0x71d6_7fff_eda6_0000;"
    x ^= (x << 17) & 0x0000_0003_eda6_0000;
    x ^= (x << 17) & 0x0006_7ffc_0000_0000;
    x ^= (x << 17) & 0x71d0_0000_0000_0000;

    // reverse "x ^= (x >> 29) & 0x5555_5555_5555_5555;"
    x ^= (x >> 29) & 0x0000_0005_5555_5540;
    x ^= (x >> 29) & 0x0000_0000_0000_0015;

    x
}

impl Default for MT19937_64 {
    #[inline]
    fn default() -> MT19937_64 {
        MT19937_64::new_unseeded()
    }
}

#[cfg(test)]
mod tests {
    use quickcheck_macros::quickcheck;
    use rand_core::{RngCore, SeedableRng};
    use std::num::Wrapping;

    use super::MT19937_64;
    use crate::vectors::mt64 as vectors;

    #[test]
    fn test_64bit_seeded() {
        let mt = MT19937_64::from_seed(0x0123_4567_89ab_cdef_u64.to_ne_bytes());
        for (&Wrapping(x), &y) in mt.state.iter().zip(vectors::STATE_SEEDED_BY_U64.iter()) {
            assert!(x == y);
        }
    }

    #[test]
    fn test_64bit_slice_seeded() {
        let mut mt = MT19937_64::default();
        mt.reseed_from_slice(
            &[
                0x12345_u64.to_ne_bytes(),
                0x23456_u64.to_ne_bytes(),
                0x34567_u64.to_ne_bytes(),
                0x45678_u64.to_ne_bytes(),
            ][..],
        );
        for (&Wrapping(x), &y) in mt.state.iter().zip(vectors::STATE_SEEDED_BY_SLICE.iter()) {
            assert!(x == y);
        }
    }

    #[test]
    fn test_64bit_output() {
        let mut mt = MT19937_64::default();
        mt.reseed_from_slice(
            &[
                0x12345_u64.to_ne_bytes(),
                0x23456_u64.to_ne_bytes(),
                0x34567_u64.to_ne_bytes(),
                0x45678_u64.to_ne_bytes(),
            ][..],
        );
        for x in vectors::TEST_OUTPUT.iter() {
            assert!(mt.next_u64() == *x);
        }
    }

    #[quickcheck]
    fn test_untemper(x: u64) -> bool {
        x == super::untemper(super::temper(x))
    }

    #[quickcheck]
    fn test_recovery(seed: u64, skip: u8) -> bool {
        let mut orig_mt = MT19937_64::from_seed(seed.to_ne_bytes());
        // skip some samples so the RNG is in an intermediate state
        for _ in 0..skip {
            orig_mt.next_u64();
        }
        let mut samples = Vec::with_capacity(super::NN);
        for _ in 0..super::NN {
            samples.push(orig_mt.next_u64().to_ne_bytes());
        }
        let mut recovered_mt = MT19937_64::recover(&samples[..]).unwrap();
        for _ in 0..super::NN * 2 {
            if orig_mt.next_u64() != recovered_mt.next_u64() {
                return false;
            }
        }
        true
    }
}
