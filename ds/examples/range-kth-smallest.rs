// https://judge.yosupo.jp/problem/range_kth_smallest
use cpio::{putln, scan};
use ds::WaveletMatrix;

fn main() {
    scan!(
        n: usize,
        q: usize,
        a: [u64; n],
        p: [(usize, usize, usize); q]
    );

    let wm = WaveletMatrix::<u64>::from(a);

    for (l, r, k) in p {
        putln!(wm.nth_smallest(k, l..r).unwrap());
    }
}
