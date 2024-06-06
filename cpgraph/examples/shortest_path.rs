// https://judge.yosupo.jp/problem/shortest_path
use cpgraph::FixedGraph;
use cpio::*;

fn main() {
    scan!(
        n: usize,
        m: usize,
        s: usize,
        t: usize,
        e: [(usize, usize, usize); m]
    );

    let graph = FixedGraph::<usize, true>::from((n, e));
    if let Some((w, path)) = graph.shortest_path(s, t) {
        putln!(w, path.len() - 1, @sep = " ");
        for v in path.windows(2) {
            putln!(v[0], v[1], @sep = " ");
        }
    } else {
        putln!(-1);
    }
}
