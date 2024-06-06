// https://judge.yosupo.jp/problem/tree_diameter
use cpgraph::FixedTree;
use cpio::*;

fn main() {
    scan!(n: usize, e: [(usize, usize, usize); n - 1]);

    let tree = FixedTree::<usize, false>::try_from((n, e)).unwrap();
    let diameter = tree.diameter();

    putln!(diameter.cost(), diameter.num_vertexes(), @sep = " ");
    putln!(diameter.path().collect::<Vec<_>>(), @sep = " ");
}
