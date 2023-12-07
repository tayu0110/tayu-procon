// https://judge.yosupo.jp/problem/point_add_range_sum
use iolib::{putln, scan};
use segtree::SegmentTree;

fn main() {
    scan!(n: usize, q: usize, a: [usize; n]);

    let mut st = SegmentTree::from_vec(&a, 0, |l, r| l + r);

    for _ in 0..q {
        scan!(t: usize);
        if t == 0 {
            scan!(p: usize, x: usize);
            st.update_by(p, x, |old, val| old + val);
        } else {
            scan!(l: usize, r: usize);
            putln!(st.foldl(l, r));
        }
    }
}
