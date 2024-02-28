// tests/python_reproducibility.rs

use rand_mt::MtPython;

// ```console
// $ python -c " \
// import random; \
// random.seed(1); \
// print(bytearray(random.randbytes(1))[0])"
// 34
// ```
// #[test]
// fn spec_bytes() {
//     let mut rng = MtPython::new(1);
//     let mut buf = [0; 1];
//     rng.fill_bytes(&mut buf);
//     println!("{:?}", buf);
// }

// ```python
// import random
// random.seed(1)
// n = random.getrandbits(128)
// ```
#[test]
fn getrandbits() {
    let mut rng = MtPython::new(1);
    let n = rng.getrandbits(128);

    assert_eq!(n, 272996653310673477252411125948039410165);
}

// ```python
// import random
// random.seed(1)
// a = list(random.randbytes(3))
// b = list(random.randbytes(32))
// c = list(random.randbytes(64))
// d = list(random.randbytes(128))
// ```
#[test]
fn fill_bytes() {
    let mut rng = MtPython::new(1);

    macro_rules! test_array {
        ($comp: expr) => {
            let mut buf = [0u8; $comp.len()];
            rng.fill_bytes(&mut buf);
            assert_eq!(buf, $comp);
        };
    }

    // a
    test_array!([177, 101, 34]);

    // b
    test_array!([
        74, 88, 183, 145, 223, 106, 241, 216, 48, 62, 97, 205, 196, 187, 134, 195, 209, 196, 39,
        16, 60, 52, 76, 65, 137, 235, 47, 30, 123, 213, 212, 126,
    ]);

    // c
    test_array!([
        68, 111, 206, 194, 163, 216, 17, 115, 97, 16, 229, 120, 27, 204, 206, 166, 150, 118, 46,
        97, 22, 198, 233, 201, 45, 153, 191, 53, 140, 46, 7, 24, 130, 44, 228, 124, 168, 199, 65,
        7, 230, 108, 176, 228, 178, 179, 244, 213, 141, 130, 202, 99, 134, 210, 201, 110, 118, 14,
        129, 155, 133, 201, 36, 195,
    ]);

    // d
    test_array!([
        89, 113, 100, 196, 166, 5, 138, 0, 88, 26, 34, 178, 45, 229, 4, 114, 67, 61, 46, 68, 254,
        216, 182, 184, 53, 126, 68, 205, 49, 41, 144, 58, 193, 212, 85, 151, 162, 66, 253, 241, 31,
        143, 43, 26, 57, 243, 195, 230, 147, 17, 67, 81, 220, 190, 212, 7, 227, 230, 182, 5, 185,
        158, 131, 6, 221, 167, 72, 166, 30, 2, 154, 138, 63, 65, 91, 2, 74, 20, 108, 240, 217, 138,
        152, 225, 207, 153, 150, 97, 249, 103, 189, 175, 223, 14, 115, 55, 66, 12, 19, 248, 245,
        212, 15, 108, 224, 121, 209, 185, 135, 55, 111, 7, 188, 184, 18, 135, 253, 200, 192, 56,
        143, 232, 129, 195, 160, 102, 25, 112,
    ]);
}
