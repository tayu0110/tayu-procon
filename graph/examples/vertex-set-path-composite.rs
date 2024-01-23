// https://judge.yosupo.jp/problem/vertex_set_path_composite
use graph::HeavyLightDecomposition;
use graph::PathVertex;
use iolib::{putln, scan};
use montgomery_modint::{Mod998244353, MontgomeryModint};
use segtree::{Monoid, Reversible, SegmentTree};

type Modint = MontgomeryModint<Mod998244353>;

#[derive(Debug, Clone)]
struct Affine {
    a: Modint,
    b: Modint,
}

impl Monoid for Affine {
    type M = Self;
    fn id() -> Self::M {
        Affine { a: Modint::one(), b: Modint::zero() }
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        Affine { a: r.a * l.a, b: r.a * l.b + r.b }
    }
}

fn main() {
    scan!(
        n: usize,
        q: usize,
        p: [(u32, u32); n],
        e: [(usize, usize); n - 1]
    );

    let hld = HeavyLightDecomposition::from_edges(n, e);
    let mut st = SegmentTree::<Reversible<Affine>>::from_vec(p.into_iter().enumerate().fold(
        vec![Reversible::new(Affine::id()); n],
        |mut s, (i, (a, b))| {
            s[hld.index(i)] = Reversible::new(Affine { a: Modint::new(a), b: Modint::new(b) });
            s
        },
    ));

    for _ in 0..q {
        scan!(t: usize);

        if t == 0 {
            scan!(p: usize, c: u32, d: u32);
            let idx = hld.index(p);
            st.set(idx, Reversible::new(Affine { a: c.into(), b: d.into() }));
        } else {
            scan!(u: usize, v: usize, x: u32);

            let (mut a, mut b) = (Modint::one(), Modint::zero());
            for path in hld.path_vertex_ranges(u, v) {
                match path {
                    PathVertex::Range { from, to } => {
                        let res = st.fold(from.min(to)..=from.max(to));
                        let res = if from <= to { res.forward } else { res.reverse };
                        let Affine { a: c, b: d } = Affine::op(&Affine { a, b }, &res);
                        (a, b) = (c, d);
                    }
                    _ => unreachable!(),
                };
            }

            putln!((a * x.into() + b).val());
        }
    }
}
