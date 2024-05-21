// https://judge.yosupo.jp/problem/static_range_count_distinct
use ds::WaveletMatrix;
use iolib::*;

fn main() {
    scan!(n: usize, q: usize, a: [u32; n], query: [(usize, usize); q]);

    let mut iota = (0..n).collect::<Vec<usize>>();
    iota.sort_unstable_by_key(|&i| (a[i], i));

    let mut prev = vec![0; n];
    for v in iota.windows(2) {
        if a[v[0]] == a[v[1]] {
            prev[v[1]] = v[0] as u32 + 1;
        }
    }

    let wm = WaveletMatrix::from(prev);

    for (l, r) in query {
        putln!(wm.count_within(..=l as u32, l..r));
    }
}
