// https://judge.yosupo.jp/problem/lca
use ds::NoOpLinkCutTree;
use iolib::{putln, scan};

fn main() {
    scan!(n: usize, q: usize);

    let mut lct = NoOpLinkCutTree::new(n);
    for i in 1..n {
        scan!(p: usize);
        lct.link(p, i).unwrap();
    }

    for _ in 0..q {
        scan!(u: usize, v: usize);

        putln!(lct.lca(u, v).unwrap());
    }
}
