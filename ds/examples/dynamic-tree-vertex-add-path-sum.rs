// https://judge.yosupo.jp/problem/dynamic_tree_vertex_add_path_sum
use ds::{LinkCutTree, MapMonoid};
use iolib::{putln, scan};

#[derive(Debug)]
struct DynamicTreeVertexAddPathSum;

impl MapMonoid for DynamicTreeVertexAddPathSum {
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

type Lct = LinkCutTree<DynamicTreeVertexAddPathSum>;

fn main() {
    scan!(n: usize, q: usize);

    let mut lct = Lct::new(n);
    for index in 0..n {
        scan!(a: u64);
        lct.set(index, a);
    }

    for _ in 0..n - 1 {
        scan!(u: usize, v: usize);
        lct.link_flat(u, v).unwrap();
    }

    for _ in 0..q {
        scan!(ty: u8);

        if ty == 0 {
            scan!(u: usize, v: usize, w: usize, x: usize);

            lct.try_cut(u, v).unwrap();
            lct.link_flat(w, x).unwrap();
        } else if ty == 1 {
            scan!(p: usize, x: u64);
            lct.update_by(p, |a| a + x);
        } else {
            scan!(u: usize, v: usize);
            putln!(*lct.fold(u, v).unwrap());
        }
    }
}
