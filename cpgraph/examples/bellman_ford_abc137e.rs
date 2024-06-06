// https://atcoder.jp/contests/abc137/tasks/abc137_e
use cpgraph::FixedGraph;
use cpio::*;

fn main() {
    scan!(n: usize, m: usize, p: i64, e: [(usize, usize, i64); m]);

    let graph =
        FixedGraph::<i64, true>::from((n, e.into_iter().map(|(a, b, c)| (a - 1, b - 1, p - c))));

    let res = graph.bellman_ford(0);
    let cost = res.cost(n - 1).unwrap();
    if cost == i64::MIN {
        putln!(-1);
    } else {
        putln!(0i64.max(-cost));
    }
}
