// https://judge.yosupo.jp/problem/dynamic_tree_vertex_set_path_composite
use cpio::{putln, scan};
use ds::{LinkCutTree, MapMonoid};
use static_modint::{Mod998244353, StaticModint};

type Modint = StaticModint<Mod998244353>;

#[derive(Debug)]
struct DynamicTreeVertexSetPathComposite;

impl MapMonoid for DynamicTreeVertexSetPathComposite {
    type M = (Modint, Modint, Modint, Modint);
    type Act = ();

    fn e() -> Self::M {
        (Modint::one(), Modint::zero(), Modint::one(), Modint::zero())
    }

    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        fn f(a: Modint, b: Modint, c: Modint, d: Modint) -> (Modint, Modint) {
            (c * a, c * b + d)
        }
        let (a, b) = f(l.0, l.1, r.0, r.1);
        let (c, d) = f(r.2, r.3, l.2, l.3);
        (a, b, c, d)
    }

    fn id() -> Self::Act {}

    fn map(m: &Self::M, _: &Self::Act) -> Self::M {
        *m
    }

    fn composite(_: &Self::Act, _: &Self::Act) -> Self::Act {}

    fn reverse(m: &mut Self::M) {
        *m = (m.2, m.3, m.0, m.1);
    }
}

fn main() {
    scan!(n: usize, q: usize);

    let mut lct = LinkCutTree::<DynamicTreeVertexSetPathComposite>::new(n);

    for i in 0..n {
        scan!(a: u32, b: u32);
        lct.set(
            i,
            (
                Modint::raw(a),
                Modint::raw(b),
                Modint::raw(a),
                Modint::raw(b),
            ),
        );
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
            scan!(p: usize, c: u32, d: u32);
            lct.set(
                p,
                (
                    Modint::raw(c),
                    Modint::raw(d),
                    Modint::raw(c),
                    Modint::raw(d),
                ),
            );
        } else {
            scan!(u: usize, v: usize, x: u32);
            let &(a, b, _, _) = lct.fold(u, v).unwrap();
            putln!((a * Modint::raw(x) + b).val());
        }
    }
}
