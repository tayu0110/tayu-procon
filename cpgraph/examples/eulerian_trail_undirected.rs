// https://judge.yosupo.jp/problem/eulerian_trail_undirected
use cpgraph::FixedGraph;
use cpio::*;

fn main() {
    scan!(t: usize);

    for _ in 0..t {
        scan!(n: usize, m: usize, e: [(usize, usize); m]);

        let graph = FixedGraph::<(), false>::from((n, e));
        if let Some((v, e)) = graph.eulerian_trail() {
            putln!("Yes");
            putln!(v, @sep = " ");
            putln!(e, @sep = " ");
        } else {
            putln!("No");
        }
    }
}
