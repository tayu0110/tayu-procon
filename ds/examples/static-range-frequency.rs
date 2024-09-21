// https://judge.yosupo.jp/problem/static_range_frequency
use cpio::{putln, scan};
use ds::WaveletMatrix;

fn main() {
    scan!(n: usize, q: usize, a: [u32; n]);

    let wm = WaveletMatrix::from(a);
    for _ in 0..q {
        scan!(l: usize, r: usize, x: u32);
        putln!(wm.countk(x, l..r));
    }
}
