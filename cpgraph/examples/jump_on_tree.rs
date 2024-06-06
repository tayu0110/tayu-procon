// https://judge.yosupo.jp/problem/jump_on_tree
use cpgraph::FixedTree;
use cpio::*;

fn main() {
    scan!(n: usize, q: usize, e: [(usize, usize); n - 1]);

    let tree = FixedTree::<(), false>::try_from((n, e)).unwrap();
    let jump = tree.jump();

    for _ in 0..q {
        scan!(s: usize, t: usize, i: usize);

        if let Some(res) = jump(s, t, i) {
            putln!(res);
        } else {
            putln!(-1);
        }
    }
}
