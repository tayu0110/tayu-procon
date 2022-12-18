// https://atcoder.jp/contests/abc239/tasks/abc239_g
use flow::Dinic;
use proconio::input;

fn main() {
    input! {n: usize, m: usize, e: [(usize, usize); m], c: [i64; n]}

    // in: i, out: i+n
    let mut ff = Dinic::new(2 * n);
    for (a, b) in e.into_iter().map(|(a, b)| (a - 1, b - 1)) {
        ff.set_edge(a + n, b, std::i64::MAX);
        ff.set_edge(b + n, a, std::i64::MAX);
    }

    for (i, c) in c.into_iter().enumerate() {
        ff.set_edge(i, i + n, c);
    }

    let c = ff.flow(n, n - 1);

    let mut min_cut_edges = ff
        .min_cut_restoration()
        .into_iter()
        .map(|(from, e)| (from, e.to))
        .filter(|&(f, t)| (f + n == t || t + n == f) && std::cmp::min(f, t) != n - 1 && std::cmp::min(f, t) != 0)
        .map(|(f, t)| std::cmp::min(f, t) + 1)
        .collect::<Vec<_>>();
    min_cut_edges.sort();
    min_cut_edges.dedup();

    println!("{}", c);
    println!("{}", min_cut_edges.len());
    if min_cut_edges.len() > 0 {
        print!("{}", min_cut_edges[0]);
        for res in min_cut_edges.into_iter().skip(1) {
            print!(" {}", res);
        }
        println!("");
    }
}
