// https://judge.yosupo.jp/problem/vertex_add_subtree_sum
use cpio::{putln, scan};
use ds::{EulerTourTree, MapMonoid};

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
    scan!(n: usize, q: usize, a: [u64; n], p: [usize; n - 1]);

    let mut ett = EulerTourTree::<U64Add>::from_edges_with_values(
        n,
        p.iter().cloned().zip(1..),
        a.into_iter().enumerate(),
    )
    .unwrap();

    ett.reroot(0);

    for _ in 0..q {
        scan!(ty: u8);

        if ty == 0 {
            scan!(u: usize, x: u64);
            ett.update_by(u, |m| m + x);
        } else {
            scan!(u: usize);
            if u > 0 {
                putln!(ett.fold_subtree(u, p[u - 1]).unwrap());
            } else {
                putln!(ett.fold(0));
            }
        }
    }
}
