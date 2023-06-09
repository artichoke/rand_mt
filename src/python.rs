// src/python.rs
//
// Copyright (c) 2015,2017 rust-mersenne-twister developers
// Copyright (c) 2020 Ryan Lopopolo <rjl@hyperbo.la>
// Copyright (c) 2023 Ignacy Sewastianowicz
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE> or <http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT> or <http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

use core::fmt::Debug;

use crate::Mt19937GenRand32;

/// CPython compatible implementation of the Mersenne Twister pseudorandom
/// number generator.
/// 
/// It is esentially a [Mt19937GenRand32] with slight modifications to match
/// behavior of the CPython's `random` module.
///
/// # Size
///
/// `Mt19937GenRandPython` requires approximately 2.5 kilobytes of internal state.
///
/// You may wish to store an `Mt19937GenRandPython` on the heap in a [`Box`] to make
/// it easier to embed in another struct.
///
/// `Mt19937GenRandPython` is also the same size as
/// [`Mt19937GenRand32`](crate::Mt19937GenRand32) and
/// [`Mt19937GenRand64`](crate::Mt19937GenRand64)
///
/// ```
/// # use core::mem;
/// # use rand_mt::{Mt19937GenRand32, Mt19937GenRand64, Mt19937GenRandPython};
/// assert_eq!(2504, mem::size_of::<Mt19937GenRandPython>());
/// assert_eq!(mem::size_of::<Mt19937GenRand64>(), mem::size_of::<Mt19937GenRand32>());
/// assert_eq!(mem::size_of::<Mt19937GenRand64>(), mem::size_of::<Mt19937GenRandPython>());
/// ```
#[derive(Clone, Hash, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct Mt19937GenRandPython {
    inner: Mt19937GenRand32,
}

impl Mt19937GenRandPython {
    /// Create a new Mersenne Twister random number generator using the given
    /// seed.
    ///
    /// This is equivalent to [random.seed](https://github.com/python/cpython/blob/3.11/Modules/_randommodule.c#L275) in CPython.
    ///
    /// # Examples: TODO
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
    #[inline]
    #[must_use]
    pub fn new(seed: u32) -> Self {
        let key: [u32; 1] = [seed];
        Self::new_with_key(key.iter().copied())
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
        Self {
            inner: Mt19937GenRand32::new_with_key(key),
        }
    }

    /// Generate next 'f64' output.
    ///
    /// This function will generate a random number on 0..1
    /// with 53 bit resolution
    ///
    /// It is compatible with CPython's `random.random`
    ///
    /// CPython implementation: <https://github.com/python/cpython/blob/3.11/Modules/_randommodule.c#L181>
    ///
    /// # Examples: TODO
    ///
    /// ```
    /// # use rand_mt::Mt19937GenRandPython;
    /// let mut mt = Mt19937GenRandPython::new(1);
    /// assert_ne!(mt.next_f64(), mt.next_f64());
    /// ```
    #[inline]
    pub fn next_f64(&mut self) -> f64 {
        let a = self.inner.next_u32() >> 5;
        let b = self.inner.next_u32() >> 6;

        (a as f64 * 67108864.0 + b as f64) * (1.0 / 9007199254740992.0)
    }

    /// Get n random bytes converted into an integer.
    ///
    /// This method is compatible with CPython's `random.getrandbits` for n <= 128
    ///
    /// # Examples: TODO
    ///
    /// # Panics
    ///
    /// The function panics if n is bigger than 128
    ///
    pub fn getrandbits(&mut self, n: usize) -> u128 {
        if n > 128 {
            panic!(
                "Can't generate higher integer than 128 bits. {} bits were given.",
                n
            );
        } else if n <= 32 {
            return (self.inner.next_u32() >> (32 - n)) as u128;
        } else if n == 0 {
            return 0;
        }

        let mut result: u128 = 0;
        let mut shift: u128 = 0;

        let mut j = n as i32;
        let words = (n - 1) / 32 + 1;
        for _ in 0..words {
            let mut r = self.inner.next_u32();
            if j < 32 {
                r >>= 32 - j;
            }

            result |= (r as u128) << shift;

            shift += 32;
            if shift >= 128 {
                break;
            }

            j -= 32;
        }

        return result;
    }

    /// Fill a buffer with bytes generated from the RNG.
    ///
    /// This method generates random `u32`s (the native output unit of the RNG)
    /// until `dest` is filled.
    ///
    /// It is compatible with CPython's `random.randbytes`
    ///
    /// # Examples: TODO
    ///
    pub fn fill_bytes(&mut self, dest: &mut [u8]) {
        let words = dest.len() + 15 / 16;
        for i in 0..words {
            let start = i * 16;
            let end = usize::min(start + 16, dest.len());

            let n = end as isize - start as isize;
            if n <= 0 {
                break;
            }
            let n = n as usize;

            let bytes = self.getrandbits(n * 8).to_le_bytes();
            for j in start..end {
                dest[j] = bytes[j - start]
            }
        }
    }
}
