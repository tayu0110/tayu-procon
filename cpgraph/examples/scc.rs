// https://judge.yosupo.jp/problem/scc
use cpgraph::FixedGraph;
use cpio::*;

fn main() {
    scan!(n: usize, m: usize, e: [(usize, usize); m]);

    let graph = FixedGraph::<(), true>::from((n, e));
    let scc = graph.scc();
    putln!(scc.len());
    for g in scc {
        putln!(g.len(), g, @sep = " ");
    }
}
