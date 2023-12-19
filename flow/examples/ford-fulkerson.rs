// https://atcoder.jp/contests/abc010/tasks/abc010_4
use flow::FordFulkerson;
use proconio::input;

fn main() {
    input! {n: usize, g: usize, e: usize, p: [usize; g], e: [(usize, usize); e]}

    let mut ff = FordFulkerson::new(n + 1);
    for (a, b) in e {
        ff.set_edge(a, b, 1);
        ff.set_edge(b, a, 1);
    }

    for p in p {
        ff.set_edge(p, n, 1);
    }

    let f = ff.flow(0, n);

    println!("{}", f);
}
