// https://atcoder.jp/contests/abc223/tasks/abc223_d
use cpgraph::FixedGraph;
use cpio::*;

fn main() {
    scan!(n: usize, m: usize, e: [(usize, usize); m]);

    let graph = FixedGraph::<(), true>::from((n, e.into_iter().map(|(a, b)| (a - 1, b - 1))));
    if let Some(topo) = graph.topological_sort() {
        putln!(topo.iter().map(|a| a + 1), @sep = " ");
    } else {
        putln!(-1);
    }
}
