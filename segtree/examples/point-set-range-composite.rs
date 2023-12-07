// https://judge.yosupo.jp/problem/point_set_range_composite
use iolib::{putln, scan};
use segtree::{Monoid, SegmentTree};
use static_modint::{Mod998244353, StaticModint};

type Modint = StaticModint<Mod998244353>;

struct Composite;
impl Monoid for Composite {
    type M = (Modint, Modint);
    fn id() -> Self::M {
        (Modint::one(), Modint::zero())
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        let (a1, a2) = *l;
        let (b1, b2) = *r;
        (b1 * a1, a2 * b1 + b2)
    }
}

fn main() {
    scan!(n: usize, q: usize, p: [(u32, u32); n],);

    let mut st = SegmentTree::<Composite>::from_vec(
        p.into_iter()
            .map(|p| (Modint::raw(p.0), Modint::raw(p.1)))
            .collect(),
    );

    for _ in 0..q {
        scan!(ty: u8);
        if ty == 0 {
            scan!(p: usize, c: u32, d: u32);
            st.set(p, (Modint::raw(c), Modint::raw(d)));
        } else {
            scan!(l: usize, r: usize, x: u32);
            let (a, b) = st.fold(l..r);
            putln!((a * Modint::raw(x) + b).val());
        }
    }
}
