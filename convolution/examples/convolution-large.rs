// https://judge.yosupo.jp/problem/convolution_mod_large
use convolution::convolution_large;
use iolib::{putvln, scan};

fn main() {
    scan!(n: usize, m: usize, a: [u32; n], b: [u32; m]);

    let c = convolution_large(a, b);

    putvln!(c, sep = ' ');
}
