// src/mt/rand.rs
//
// Copyright (c) 2015,2017 rust-mersenne-twister developers
// Copyright (c) 2020 Ryan Lopopolo <rjl@hyperbo.la>
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE> or <http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT> or <http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

use rand_core::{Infallible, SeedableRng, TryRng};

use super::Mt;

impl SeedableRng for Mt {
    type Seed = [u8; 4];

    /// Reseed from a little endian encoded `u32`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rand_core::{Rng, SeedableRng};
    /// use rand_mt::Mt;
    ///
    /// // Default MT seed
    /// let seed = 5489_u32.to_le_bytes();
    /// let mut rng = Mt::from_seed(seed);
    /// # fn example<T: Rng>(mut rng: T) {
    /// assert_ne!(rng.next_u32(), rng.next_u32());
    /// # }
    /// # example(rng);
    /// ```
    #[inline]
    fn from_seed(seed: Self::Seed) -> Self {
        Self::from(seed)
    }
}

impl TryRng for Mt {
    type Error = Infallible;

    /// Generate next `u64` output.
    ///
    /// This function is implemented by generating two `u32`s from the RNG and
    /// performing shifting and masking to turn them into a `u64` output.
    ///
    /// # Examples
    ///
    /// ```
    /// use rand_core::Rng;
    /// use rand_mt::Mt;
    ///
    /// let mut rng = Mt::new_unseeded();
    /// # fn example<T: Rng>(mut rng: T) {
    /// assert_ne!(rng.next_u64(), rng.next_u64());
    /// # }
    /// # example(rng);
    /// ```
    #[inline]
    fn try_next_u64(&mut self) -> Result<u64, Self::Error> {
        Ok(Self::next_u64(self))
    }

    /// Generate next `u32` output.
    ///
    /// `u32` is the native output of the generator. This function advances the
    /// RNG step counter by one.
    ///
    /// # Examples
    ///
    /// ```
    /// use rand_core::Rng;
    /// use rand_mt::Mt;
    ///
    /// let mut rng = Mt::new_unseeded();
    /// # fn example<T: Rng>(mut rng: T) {
    /// assert_ne!(rng.next_u32(), rng.next_u32());
    /// # }
    /// # example(rng);
    /// ```
    #[inline]
    fn try_next_u32(&mut self) -> Result<u32, Self::Error> {
        Ok(Self::next_u32(self))
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
    /// use rand_core::Rng;
    /// use rand_mt::Mt;
    ///
    /// let mut rng = Mt::new_unseeded();
    /// # fn example<T: Rng>(mut rng: T) {
    /// let mut buf = [0; 32];
    /// rng.fill_bytes(&mut buf);
    /// assert_ne!([0; 32], buf);
    /// let mut buf = [0; 31];
    /// rng.fill_bytes(&mut buf);
    /// assert_ne!([0; 31], buf);
    /// # }
    /// # example(rng);
    /// ```
    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Self::Error> {
        Self::fill_bytes(self, dest);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use core::num::Wrapping;
    use rand_core::{Rng, SeedableRng};

    use super::Mt;
    use crate::vectors::mt::{STATE_SEEDED_BY_U32, TEST_OUTPUT};

    #[test]
    fn seeded_state_from_u32_seed() {
        let rng = Mt::new(0x1234_5678_u32);
        let rng_from_seed = Mt::from_seed(0x1234_5678_u32.to_le_bytes());
        assert_eq!(rng.state, rng_from_seed.state);
        for (&Wrapping(x), &y) in rng.state.iter().zip(STATE_SEEDED_BY_U32.iter()) {
            assert_eq!(x, y);
        }
        for (&Wrapping(x), &y) in rng_from_seed.state.iter().zip(STATE_SEEDED_BY_U32.iter()) {
            assert_eq!(x, y);
        }
    }

    #[test]
    fn output_from_u32_slice_key() {
        let key = [0x123_u32, 0x234_u32, 0x345_u32, 0x456_u32];
        let mut rng = Mt::new_with_key(key.iter().copied());
        for &x in &TEST_OUTPUT {
            assert_eq!(x, Rng::next_u32(&mut rng));
        }
    }
}
