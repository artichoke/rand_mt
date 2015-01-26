# Mersenne Twister in Rust

This is a pure rust port of the
[Mersenne Twister](http://www.math.sci.hiroshima-u.ac.jp/~m-mat/MT/emt.html)
pseudorandom number generators. See the rustdoc for suggested usage.

## Algorithms Implemented

- MT19937 (32-bit version)
- MT19937-64 (64-bit version)

## Stability

Rust's random number generator interfaces are unstable, and this
crate's interface will continue to evolve with them.
