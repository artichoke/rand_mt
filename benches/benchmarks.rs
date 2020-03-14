#![feature(test)]
extern crate test;

extern crate mersenne_twister;
extern crate rand;

mod mt19937 {
    use mersenne_twister::MT19937;
    use rand::Rng;

    #[bench]
    fn benchmark_seeding(b: &mut ::test::Bencher) {
        b.iter(|| MT19937::new_unseeded());
    }

    #[bench]
    fn benchmark_fill_next_state(b: &mut ::test::Bencher) {
        let mt = MT19937::new_unseeded();
        b.iter(|| {
            let mut mt = mt.clone();
            // Note that the first call to next_u32() triggers a call
            // to the fill_next_state() method, which is really what I
            // want to benchmark here.
            mt.next_u32();
        })
    }
}

mod mt19937_64 {
    use mersenne_twister::MT19937_64;
    use rand::Rng;

    #[bench]
    fn benchmark_seeding(b: &mut ::test::Bencher) {
        b.iter(|| MT19937_64::new_unseeded());
    }

    #[bench]
    fn benchmark_fill_next_state(b: &mut ::test::Bencher) {
        let mt = MT19937_64::new_unseeded();
        b.iter(|| {
            let mut mt = mt.clone();
            // Note that the first call to next_u32() triggers a call
            // to the fill_next_state() method, which is really what I
            // want to benchmark here.
            mt.next_u64();
        })
    }
}
