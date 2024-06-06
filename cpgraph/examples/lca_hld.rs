// https://judge.yosupo.jp/problem/lca
use cpgraph::FixedTree;
use cpio::*;

fn main() {
    scan!(n: usize, q: usize, p: [usize; n - 1]);

    let tree =
        FixedTree::<(), false>::try_from((n, p.into_iter().enumerate().map(|(i, p)| (i + 1, p))))
            .unwrap();
    let hld = tree.heavy_light_decomposition(0);

    for _ in 0..q {
        scan!(u: usize, v: usize);
        putln!(hld.lca(u, v));
    }
}
