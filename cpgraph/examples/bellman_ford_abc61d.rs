// https://atcoder.jp/contests/abc061/tasks/abc061_d
use cpgraph::FixedGraph;
use cpio::*;

fn main() {
    scan!(n: usize, m: usize, e: [(usize, usize, i64); m]);

    let graph =
        FixedGraph::<i64, true>::from((n, e.into_iter().map(|(a, b, c)| (a - 1, b - 1, -c))));

    let res = graph.bellman_ford(0);
    let cost = res.cost(n - 1).unwrap();
    if cost == i64::MIN {
        putln!("inf");
    } else {
        putln!(-cost);
    }
}
