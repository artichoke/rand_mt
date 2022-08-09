// tests/ruby_reproducibility.rs
//
// Copyright (c) 2015,2017 rust-mersenne-twister developers
// Copyright (c) 2020 Ryan Lopopolo <rjl@hyperbo.la>
//
// Licensed under the Apache License, Version 2.0
// <LICENSE-APACHE or http://www.apache.org/licenses/LICENSE-2.0> or the MIT
// license <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. All files in the project carrying such notice may not be copied,
// modified, or distributed except according to those terms.

use rand_mt::Mt;

// # ruby/spec Random
//
// ```ruby
// # Should double check this is official spec
// it "returns the same numeric output for a given seed across all implementations and platforms" do
//   rnd = Random.new(33)
//   rnd.bytes(2).should == "\x14\\"
//   rnd.bytes(1000) # skip some
//   rnd.bytes(2).should == "\xA1p"
// end
// ```
#[test]
fn spec_bytes() {
    let mut rng = Mt::new(33);
    let mut buf = [0; 2];
    rng.fill_bytes(&mut buf);
    assert_eq!(buf[..], b"\x14\\"[..]);

    let mut skip = [0; 1000];
    rng.fill_bytes(&mut skip);

    let mut buf = [0; 2];
    rng.fill_bytes(&mut buf);
    assert_eq!(buf[..], b"\xA1p"[..]);
}

// # MSpec helpers
//
// ```ruby
// def bignum_value(plus = 0)
//   0x8000_0000_0000_0000 + plus
// end
// ```
//
// # ruby/spec Random
//
// ```ruby
// it "returns the same numeric output for a given huge seed across all implementations and platforms" do
//   rnd = Random.new(bignum_value ** 4)
//   rnd.bytes(2).should == "_\x91"
//   rnd.bytes(1000) # skip some
//   rnd.bytes(2).should == "\x17\x12"
// end
// ```
#[test]
fn spec_big_num_bytes() {
    // ```console
    // [3.1.2] > big = 0x8000_0000_0000_0000 ** 4
    // => 7237005577332262213973186563042994240829374041602535252466099000494570602496
    // [3.1.2] > bytes = big.to_s(16).split("").each_slice(8).map{|s| "0x#{s.join[0, 4]}_#{s.join[4, 4]}"}
    // => ["0x1000_0000", "0x0000_0000", "0x0000_0000", "0x0000_0000", "0x0000_0000", "0x0000_0000", "0x0000_0000", "0x0000_0000"]
    // [3.1.2] > puts bytes.inspect.gsub '"', ''
    // [0x1000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000, 0x0000_0000]
    // => nil
    // ```
    let seed: [u32; 8] = [
        0x1000_0000,
        0x0000_0000,
        0x0000_0000,
        0x0000_0000,
        0x0000_0000,
        0x0000_0000,
        0x0000_0000,
        0x0000_0000,
    ];
    // Ruby "packs" a `Bignum` into a `&mut [u32]` with least significant word
    // first and native byte order.
    //
    // https://github.com/ruby/ruby/blob/v2_6_3/random.c#L383-L384
    let mut rng = Mt::new_with_key(seed.iter().rev().copied());
    let mut buf = [0; 2];
    rng.fill_bytes(&mut buf);
    assert_eq!(buf[..], b"_\x91"[..]);

    let mut skip = [0; 1000];
    rng.fill_bytes(&mut skip);

    let mut buf = [0; 2];
    rng.fill_bytes(&mut buf);
    assert_eq!(buf[..], b"\x17\x12"[..]);
}
