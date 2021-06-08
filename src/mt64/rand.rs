use rand_core::{Error, RngCore, SeedableRng};

use super::Mt19937GenRand64;

impl SeedableRng for Mt19937GenRand64 {
    type Seed = [u8; 8];

    /// Reseed from a little endian encoded `u64`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use rand_core::{RngCore, SeedableRng};
    /// # use rand_mt::Mt19937GenRand64;
    /// // Default MT seed
    /// let seed = 5489_u64.to_le_bytes();
    /// let mut mt = Mt19937GenRand64::from_seed(seed);
    /// assert_ne!(mt.next_u64(), mt.next_u64());
    /// ```
    #[inline]
    fn from_seed(seed: Self::Seed) -> Self {
        Self::from(seed)
    }
}

impl RngCore for Mt19937GenRand64 {
    /// Generate next `u64` output.
    ///
    /// `u64` is the native output of the generator. This function advances the
    /// RNG step counter by one.
    ///
    /// # Examples
    ///
    /// ```
    /// use rand_core::RngCore;
    /// use rand_mt::Mt19937GenRand64;
    ///
    /// let mut rng = Mt19937GenRand64::new_unseeded();
    /// # fn example<T: RngCore>(mut rng: T) {
    /// assert_ne!(rng.next_u64(), rng.next_u64());
    /// # }
    /// # example(rng);
    /// ```
    #[inline]
    fn next_u64(&mut self) -> u64 {
        Self::next_u64(self)
    }

    /// Generate next `u32` output.
    ///
    /// This function is implemented by generating one `u64`s from the RNG and
    /// shifting + masking them into a `u32` output.
    ///
    /// # Examples
    ///
    /// ```
    /// use rand_core::RngCore;
    /// use rand_mt::Mt19937GenRand64;
    ///
    /// let mut rng = Mt19937GenRand64::new_unseeded();
    /// # fn example<T: RngCore>(mut rng: T) {
    /// assert_ne!(rng.next_u32(), rng.next_u32());
    /// # }
    /// # example(rng);
    /// ```
    #[inline]
    fn next_u32(&mut self) -> u32 {
        Self::next_u32(self)
    }

    /// Fill a buffer with bytes generated from the RNG.
    ///
    /// This method generates random `u64`s (the native output unit of the RNG)
    /// until `dest` is filled.
    ///
    /// This method may discard some output bits if `dest.len()` is not a
    /// multiple of 8.
    ///
    /// # Examples
    ///
    /// ```
    /// use rand_core::RngCore;
    /// use rand_mt::Mt19937GenRand64;
    ///
    /// let mut rng = Mt19937GenRand64::new_unseeded();
    /// # fn example<T: RngCore>(mut rng: T) {
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
    fn fill_bytes(&mut self, dest: &mut [u8]) {
        Self::fill_bytes(self, dest);
    }

    /// Fill a buffer with bytes generated from the RNG.
    ///
    /// This method generates random `u64`s (the native output unit of the RNG)
    /// until `dest` is filled.
    ///
    /// This method may discard some output bits if `dest.len()` is not a
    /// multiple of 8.
    ///
    /// `try_fill_bytes` is implemented with [`fill_bytes`](RngCore::fill_bytes)
    /// and is infallible.
    ///
    /// # Examples
    ///
    /// ```
    /// use rand_core::RngCore;
    /// use rand_mt::Mt19937GenRand64;
    ///
    /// let mut rng = Mt19937GenRand64::new_unseeded();
    /// # fn example<T: RngCore>(mut rng: T) -> Result<(), rand_core::Error> {
    /// let mut buf = [0; 32];
    /// rng.try_fill_bytes(&mut buf)?;
    /// assert_ne!([0; 32], buf);
    /// let mut buf = [0; 31];
    /// rng.try_fill_bytes(&mut buf)?;
    /// assert_ne!([0; 31], buf);
    /// # Ok(())
    /// # }
    /// # example(rng).unwrap()
    /// ```
    #[inline]
    fn try_fill_bytes(&mut self, dest: &mut [u8]) -> Result<(), Error> {
        Self::fill_bytes(self, dest);
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use core::num::Wrapping;
    use rand_core::{RngCore, SeedableRng};

    use super::Mt19937GenRand64;
    use crate::vectors::mt64::{STATE_SEEDED_BY_U64, TEST_OUTPUT};

    #[test]
    fn seeded_state_from_u64_seed() {
        let mt = Mt19937GenRand64::new(0x0123_4567_89ab_cdef_u64);
        let mt_from_seed = Mt19937GenRand64::from_seed(0x0123_4567_89ab_cdef_u64.to_le_bytes());
        assert_eq!(mt.state, mt_from_seed.state);
        for (&Wrapping(x), &y) in mt.state.iter().zip(STATE_SEEDED_BY_U64.iter()) {
            assert_eq!(x, y);
        }
        for (&Wrapping(x), &y) in mt_from_seed.state.iter().zip(STATE_SEEDED_BY_U64.iter()) {
            assert_eq!(x, y);
        }
    }

    #[test]
    fn output_from_u64_slice_key() {
        let key = [0x12345_u64, 0x23456_u64, 0x34567_u64, 0x45678_u64];
        let mut mt = Mt19937GenRand64::new_with_key(key.iter().copied());
        for &x in TEST_OUTPUT.iter() {
            assert_eq!(x, RngCore::next_u64(&mut mt));
        }
    }
}
