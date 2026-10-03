// tests/fill_bytes.rs
//
// Copyright (c) 2026 Ryan Lopopolo <rjl@hyperbo.la>
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

use rand_mt::{Mt, Mt64};

#[test]
fn mt_fill_bytes_preserves_stream_and_state() {
    const WORD_BYTES: usize = size_of::<u32>();
    const STATE_WORDS: usize = 624;
    // Exercise every remainder length and cross multiple twist boundaries,
    // including starting immediately before and after a state refill.
    for skip in [0, STATE_WORDS - 1, STATE_WORDS, STATE_WORDS + 1] {
        let mut initial = Mt::new_unseeded();
        for _ in 0..skip {
            initial.next_u32();
        }
        for len in 0..=2 * STATE_WORDS * WORD_BYTES + WORD_BYTES {
            let mut expected_rng = initial.clone();
            let mut expected: Vec<u8> = (0..len.div_ceil(WORD_BYTES))
                .flat_map(|_| expected_rng.next_u32().to_le_bytes())
                .collect();
            expected.truncate(len);

            let mut rng = initial.clone();
            // Guards also verify that filling a subslice leaves its neighbors alone.
            let mut bytes = vec![0xa5; len + 2];
            rng.fill_bytes(&mut bytes[1..=len]);
            assert_eq!(&bytes[1..=len], expected, "skip={skip}, len={len}");
            assert_eq!(bytes[0], 0xa5);
            assert_eq!(bytes[len + 1], 0xa5);
            assert_eq!(rng, expected_rng, "skip={skip}, len={len}");

            #[cfg(feature = "rand-traits")]
            {
                let mut trait_rng = initial.clone();
                let mut trait_bytes = vec![0; len];
                rand_core::Rng::fill_bytes(&mut trait_rng, &mut trait_bytes);
                assert_eq!(trait_bytes, expected, "skip={skip}, len={len}");
                assert_eq!(trait_rng, expected_rng, "skip={skip}, len={len}");
            }
        }
    }
}

#[test]
fn mt64_fill_bytes_preserves_stream_and_state() {
    const WORD_BYTES: usize = size_of::<u64>();
    const STATE_WORDS: usize = 312;
    // Exercise every remainder length and cross multiple twist boundaries,
    // including starting immediately before and after a state refill.
    for skip in [0, STATE_WORDS - 1, STATE_WORDS, STATE_WORDS + 1] {
        let mut initial = Mt64::new_unseeded();
        for _ in 0..skip {
            initial.next_u64();
        }
        for len in 0..=2 * STATE_WORDS * WORD_BYTES + WORD_BYTES {
            let mut expected_rng = initial.clone();
            let mut expected: Vec<u8> = (0..len.div_ceil(WORD_BYTES))
                .flat_map(|_| expected_rng.next_u64().to_le_bytes())
                .collect();
            expected.truncate(len);

            let mut rng = initial.clone();
            // Guards also verify that filling a subslice leaves its neighbors alone.
            let mut bytes = vec![0xa5; len + 2];
            rng.fill_bytes(&mut bytes[1..=len]);
            assert_eq!(&bytes[1..=len], expected, "skip={skip}, len={len}");
            assert_eq!(bytes[0], 0xa5);
            assert_eq!(bytes[len + 1], 0xa5);
            assert_eq!(rng, expected_rng, "skip={skip}, len={len}");

            #[cfg(feature = "rand-traits")]
            {
                let mut trait_rng = initial.clone();
                let mut trait_bytes = vec![0; len];
                rand_core::Rng::fill_bytes(&mut trait_rng, &mut trait_bytes);
                assert_eq!(trait_bytes, expected, "skip={skip}, len={len}");
                assert_eq!(trait_rng, expected_rng, "skip={skip}, len={len}");
            }
        }
    }
}
