// https://judge.yosupo.jp/problem/static_range_frequency
use ds::WaveletMatrix;
use iolib::{putln, scan};

fn main() {
    scan!(n: usize, q: usize, a: [u64; n]);

    let wm = WaveletMatrix::from(a);
    for _ in 0..q {
        scan!(l: usize, r: usize, x: u64);
        putln!(wm.countk(x, l..r));
    }
}
