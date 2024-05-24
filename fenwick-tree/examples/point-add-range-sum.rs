// https://judge.yosupo.jp/problem/point_add_range_sum
use fenwick_tree::{Addition, FenwickTree};
use iolib::{putln, scan};

fn main() {
    scan!(n: usize, q: usize, a: [usize; n]);

    let mut ft = FenwickTree::<Addition<usize>>::from(a);

    for _ in 0..q {
        scan!(t: usize);

        if t == 0 {
            scan!(p: usize, x: usize);
            ft.add(p, x);
        } else {
            scan!(l: usize, r: usize);
            putln!(ft.fold(l..r));
        }
    }
}
