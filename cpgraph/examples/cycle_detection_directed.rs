// https://judge.yosupo.jp/problem/cycle_detection
use cpgraph::FixedGraph;
use cpio::*;

fn main() {
    scan!(n: usize, m: usize, e: [(usize, usize); m]);

    let graph = FixedGraph::<(), true>::from((n, e));
    if let Some((_, re)) = graph.cycle_detect() {
        putln!(re.len());
        putln!(re, @sep = "\n");
    } else {
        putln!(-1);
    }
}
