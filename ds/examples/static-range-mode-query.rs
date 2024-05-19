// https://judge.yosupo.jp/problem/static_range_mode_query
use ds::WaveletMatrix;
use iolib::*;

fn main() {
    scan!(n: usize, q: usize, a: [u64; n], query: [(usize, usize); q]);

    let wm = WaveletMatrix::from(a);

    for (l, r) in query {
        let (v, freq) = wm.top_of_mode(l..r).next().unwrap();
        putitln!([v, freq as u64].into_iter(), sep = ' ');
    }
}
