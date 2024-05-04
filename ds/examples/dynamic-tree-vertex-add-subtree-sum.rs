// https://judge.yosupo.jp/problem/dynamic_tree_vertex_add_subtree_sum
use ds::{EulerTourTree, MapMonoid};
use iolib::*;

struct U64Add;

impl MapMonoid for U64Add {
    type M = u64;
    type Act = ();
    fn e() -> Self::M {
        0
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        l + r
    }
    fn id() -> Self::Act {}
    fn composite(_: &Self::Act, _: &Self::Act) -> Self::Act {}
    fn map(m: &Self::M, _: &Self::Act) -> Self::M {
        *m
    }
}

fn main() {
    scan!(n: usize, q: usize, a: [u64; n], e: [(usize, usize); n - 1]);

    let mut ett =
        EulerTourTree::<U64Add>::from_edges_with_values(n, e, a.into_iter().enumerate()).unwrap();

    for _ in 0..q {
        scan!(ty: u8);

        if ty == 0 {
            scan!(u: usize, v: usize, w: usize, x: usize);
            ett.cut(u, v);
            ett.link(w, x).unwrap();
        } else if ty == 1 {
            scan!(p: usize, x: u64);
            ett.update_by(p, |m| m + x);
        } else {
            scan!(v: usize, p: usize);
            putln!(ett.fold_subtree(v, p).unwrap());
        }
    }
}
