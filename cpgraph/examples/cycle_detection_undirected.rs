// https://judge.yosupo.jp/problem/cycle_detection_undirected
use cpgraph::FixedGraph;
use cpio::*;

fn main() {
    scan!(n: usize, m: usize, e: [(usize, usize); m]);

    let graph = FixedGraph::<(), false>::from((n, e));
    if let Some((rv, re)) = graph.cycle_detect() {
        putln!(rv.len());
        putln!(rv, @sep = " ");
        putln!(re, @sep = " ");
    } else {
        putln!(-1);
    }
}
