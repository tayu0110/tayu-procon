use ds::{EulerTourTree, MapMonoid};
// https://judge.yosupo.jp/problem/dynamic_tree_subtree_add_subtree_sum
use iolib::*;

struct U64Add;

impl MapMonoid for U64Add {
    type M = (u64, u64);
    type Act = u64;
    fn e() -> Self::M {
        (0, 0)
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        (l.0 + r.0, l.1 + r.1)
    }
    fn id() -> Self::Act {
        0
    }
    fn composite(l: &Self::Act, r: &Self::Act) -> Self::Act {
        l + r
    }
    fn map(m: &Self::M, act: &Self::Act) -> Self::M {
        (m.0 + act * m.1, m.1)
    }
}

fn main() {
    scan!(n: usize, q: usize, a: [u64; n], e: [(usize, usize); n - 1]);

    let mut ett = EulerTourTree::<U64Add>::from_edges_with_values(
        n,
        e,
        a.into_iter().map(|a| (a, 1)).enumerate(),
    )
    .unwrap();

    for _ in 0..q {
        scan!(ty: u8);

        if ty == 0 {
            scan!(u: usize, v: usize, w: usize, x: usize);
            ett.cut(u, v);
            ett.link(w, x).unwrap();
        } else if ty == 1 {
            scan!(v: usize, p: usize, x: u64);
            ett.apply_subtree(v, p, &x);
        } else {
            scan!(v: usize, p: usize);
            putln!(ett.fold_subtree(v, p).unwrap().0);
        }
    }
}
