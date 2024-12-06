// https://judge.yosupo.jp/problem/point_add_range_sum
use cpio::{putln, scan};
use ds::{Monoid, SegmentTree};

struct UsizeAdd;

impl Monoid for UsizeAdd {
    type M = usize;
    fn id() -> Self::M {
        0
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        l + r
    }
}

fn main() {
    scan!(n: usize, q: usize, a: [usize; n]);

    let mut st = SegmentTree::<UsizeAdd>::from_vec(a);

    for _ in 0..q {
        scan!(t: usize);
        if t == 0 {
            scan!(p: usize, x: usize);
            st.update_by(p, move |&old| old + x);
        } else {
            scan!(l: usize, r: usize);
            putln!(st.fold(l..r));
        }
    }
}
