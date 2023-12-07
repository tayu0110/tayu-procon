// https://judge.yosupo.jp/submission/108278
use iolib::{putln, scan};
use segtree::SegmentTree;
use static_modint::{Mod998244353, StaticModint};

type Modint = StaticModint<Mod998244353>;

fn main() {
    scan!(
        n: usize,
        q: usize,
        p: [(u32, u32); n],
        q: [(usize, usize, u32, u32); q]
    );

    let mut st = SegmentTree::from_vec(
        &p.into_iter()
            .map(|p| (Modint::raw(p.0), Modint::raw(p.1)))
            .collect(),
        (Modint::one(), Modint::zero()),
        |&(a1, b1), &(a2, b2)| (a1 * a2, a2 * b1 + b2),
    );

    for (t, l, r, x) in q {
        if t == 0 {
            st.set(l, (Modint::raw(r), Modint::raw(x)));
        } else {
            let (a, b) = st.foldr(l, r as usize);
            putln!((a * Modint::raw(x) + b).val());
        }
    }
}
