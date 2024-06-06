// https://judge.yosupo.jp/problem/two_edge_connected_components
use cpgraph::FixedGraph;
use cpio::*;

fn main() {
    scan!(n: usize, m: usize, e: [(usize, usize); m]);

    let graph = FixedGraph::<(), false>::from((n, e));
    let tecc = graph.two_edge_connected_components();
    putln!(tecc.len());
    for t in tecc {
        putln!(t.len(), t, @sep = " ");
    }
}
