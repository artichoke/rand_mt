use rand_mt::Mt;

// ```ruby
// # Should double check this is official spec
// it "returns the same numeric output for a given seed across all implementations and platforms" do
//   rnd = Random.new(33)
//   rnd.bytes(2).should == "\x14\\"
//   rnd.bytes(1000) # skip some
//   rnd.bytes(2).should == "\xA1p"
// end
//
// it "returns the same numeric output for a given huge seed across all implementations and platforms" do
//   rnd = Random.new(bignum_value ** 4)
//   rnd.bytes(2).should == "_\x91"
//   rnd.bytes(1000) # skip some
//   rnd.bytes(2).should == "\x17\x12"
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
