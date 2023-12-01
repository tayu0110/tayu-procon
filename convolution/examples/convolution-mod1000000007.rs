// https://judge.yosupo.jp/problem/convolution_mod_1000000007
use convolution::convolution_1e97;
use iolib::{putvsln, scan};

fn main() {
    scan!(n: usize, m: usize, a: [u32; n], b: [u32; m]);

    let c = convolution_1e97(a, b);

    putvsln!(c);
}
