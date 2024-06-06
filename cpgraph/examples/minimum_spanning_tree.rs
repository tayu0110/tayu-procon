// https://judge.yosupo.jp/problem/minimum_spanning_tree
use cpgraph::FixedGraph;
use cpio::*;

fn main() {
    scan!(n: usize, m: usize, e: [(usize, usize, usize); m]);

    let graph = FixedGraph::<usize, false>::from((n, e));
    let mst = graph.minimum_spanning_tree().unwrap();

    let e = mst
        .edges_all()
        .filter_map(|e| (e.from() < e.to()).then_some(e.index()))
        .collect::<Vec<_>>();
    let w = mst
        .edges_all()
        .filter_map(|e| (e.from() < e.to()).then_some(*e.weight()))
        .sum::<usize>();

    putln!(w);
    putln!(e, @sep = " ");
}
