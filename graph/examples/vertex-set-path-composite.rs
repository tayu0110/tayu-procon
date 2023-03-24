// https://judge.yosupo.jp/problem/vertex_set_path_composite
use graph::path_query;
use iolib::{putln, scan};
use montgomery_modint::{Mod998244353, MontgomeryModint};
use segtree::SegmentTree;

type Modint = MontgomeryModint<Mod998244353>;

fn main() {
    scan!(n: usize, q: usize, p: [(u32, u32); n], e: [(usize, usize); n - 1]);

    let mut t = vec![vec![]; n];
    for (u, v) in e {
        t[u].push(v);
        t[v].push(u);
    }

    let tree = t.try_into().unwrap();
    let path_query = path_query(&tree);

    let mut p = {
        let mut np = vec![(Modint::zero(), Modint::zero()); n];
        for i in 0..n {
            np[path_query(i, i)[0].0] = (p[i].0.into(), p[i].1.into());
        }

        np
    };

    let f = |&l: &(Modint, Modint), &r: &(Modint, Modint)| (r.0 * l.0, r.0 * l.1 + r.1);
    let mut st = SegmentTree::from_vec(&p, (Modint::one(), Modint::zero()), f);
    p.reverse();
    let mut st_rev = SegmentTree::from_vec(&p, (Modint::one(), Modint::zero()), f);

    for _ in 0..q {
        scan!(t: usize);

        if t == 0 {
            scan!(p: usize, c: u32, d: u32);
            let idx = path_query(p, p)[0].0;
            st.set(idx, (c.into(), d.into()));
            st_rev.set(n - 1 - idx, (c.into(), d.into()));
        } else {
            scan!(u: usize, v: usize, x: u32);
            let indices = path_query(u, v);

            let (mut a, mut b) = (Modint::one(), Modint::zero());
            for (u, v) in indices {
                let (na, nb) = if u <= v { f(&(a, b), &st.foldr(u, v + 1)) } else { f(&(a, b), &st_rev.foldr(n - 1 - u, n - v)) };
                a = na;
                b = nb;
            }

            putln!((a * x.into() + b).val());
        }
    }
}
