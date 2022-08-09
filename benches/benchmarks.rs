// benches/benchmarks.rs
//
// Copyright (c) 2015,2017 rust-mersenne-twister developers
// Copyright (c) 2020 Ryan Lopopolo <rjl@hyperbo.la>
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

#![feature(test)]
extern crate test;

mod mt19937 {
    use rand_mt::Mt;

    #[bench]
    fn benchmark_seeding(b: &mut ::test::Bencher) {
        b.iter(Mt::new_unseeded);
    }

    #[bench]
    fn benchmark_fill_next_state(b: &mut ::test::Bencher) {
        b.iter(|| {
            let mut mt = Mt::new_unseeded();
            // Note that the first call to next_u32() triggers a call
            // to the fill_next_state() method, which is really what I
            // want to benchmark here.
            mt.next_u32();
        })
    }
}

mod mt19937_64 {
    use rand_mt::Mt64;

    #[bench]
    fn benchmark_seeding(b: &mut ::test::Bencher) {
        b.iter(Mt64::new_unseeded);
    }

    #[bench]
    fn benchmark_fill_next_state(b: &mut ::test::Bencher) {
        b.iter(|| {
            let mut mt = Mt64::new_unseeded();
            // Note that the first call to next_u64() triggers a call
            // to the fill_next_state() method, which is really what I
            // want to benchmark here.
            mt.next_u64();
        })
    }
}
