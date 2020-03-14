#![feature(test)]
extern crate test;

mod mt19937 {
    use rand_core::RngCore;
    use rand_mt::MT19937;

    #[bench]
    fn benchmark_seeding(b: &mut ::test::Bencher) {
        b.iter(MT19937::new_unseeded);
    }

    #[bench]
    fn benchmark_fill_next_state(b: &mut ::test::Bencher) {
        b.iter(|| {
            let mut mt = MT19937::new_unseeded();
            // Note that the first call to next_u32() triggers a call
            // to the fill_next_state() method, which is really what I
            // want to benchmark here.
            mt.next_u32();
        })
    }
}

mod mt19937_64 {
    use rand_core::RngCore;
    use rand_mt::MT19937_64;

    #[bench]
    fn benchmark_seeding(b: &mut ::test::Bencher) {
        b.iter(MT19937_64::new_unseeded);
    }

    #[bench]
    fn benchmark_fill_next_state(b: &mut ::test::Bencher) {
        b.iter(|| {
            let mut mt = MT19937_64::new_unseeded();
            // Note that the first call to next_u32() triggers a call
            // to the fill_next_state() method, which is really what I
            // want to benchmark here.
            mt.next_u64();
        })
    }
}
