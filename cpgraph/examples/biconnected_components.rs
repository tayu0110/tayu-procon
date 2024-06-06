// https://judge.yosupo.jp/problem/biconnected_components
use cpgraph::FixedGraph;
use cpio::*;

fn main() {
    scan!(n: usize, m: usize, e: [(usize, usize); m]);

    let graph = FixedGraph::<(), false>::from((n, e));
    let bcc = graph.biconnected_components();
    putln!(bcc.len());
    for bcc in bcc {
        putln!(bcc.len(), bcc, @sep = " ");
    }
}
