// https://judge.yosupo.jp/problem/point_add_range_sum
use iolib::scan;
use segtree::SegmentTree;

fn main() {
    scan!(n: usize, q: usize, a: [usize; n], p: [(usize, usize, usize); q]);

    let mut st = SegmentTree::new(n, 0, |l, r| *l + *r);
    for (i, v) in a.into_iter().enumerate() {
        st.set(i, v);
    }

    for (t, l, r) in p {
        if t == 0 {
            st.update_by(l, r, |old, val| *old + *val);
        } else {
            println!("{}", st.foldl(l, r));
        }
    }
}
