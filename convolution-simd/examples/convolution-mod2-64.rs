// https://judge.yosupo.jp/problem/convolution_mod_2_64
use convolution_simd::convolution_mod_2_64;
use iolib::{putvec_with_spaceln, scan};

fn main() {
    scan!(n: usize, m: usize, a: [u64; n], b: [u64; m]);

    let c = convolution_mod_2_64(a, b);

    putvec_with_spaceln!(c);
}
