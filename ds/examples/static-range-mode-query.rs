// https://judge.yosupo.jp/problem/static_range_mode_query
use cpio::*;
use ds::WaveletMatrix;

fn main() {
    scan!(n: usize, q: usize, a: [u64; n], query: [(usize, usize); q]);

    let wm = WaveletMatrix::from(a);

    for (l, r) in query {
        let (v, freq) = wm.top_of_mode(l..r).next().unwrap();
        putln!([v, freq as u64], @sep = " ");
    }
}
