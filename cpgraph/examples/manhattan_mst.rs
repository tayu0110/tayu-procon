// https://judge.yosupo.jp/problem/manhattanmst
use cpgraph::manhattan_minimum_spanning_tree;
use cpio::*;

fn main() {
    scan!(n: usize, p: [(i64, i64); n]);

    let edges = manhattan_minimum_spanning_tree(&p);
    let w = edges.iter().map(|v| v.0).sum::<i64>();

    putln!(w);
    for (_, u, v) in edges {
        putln!(u, v, @sep = " ");
    }
}
