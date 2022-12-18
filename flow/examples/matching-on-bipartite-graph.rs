// https://judge.yosupo.jp/problem/bipartitematching
use flow::maximum_matching_of_bipartite_graph;
use iolib::scan;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(l: usize, r: usize, m: usize, p: [(usize, usize); m]);
    let p = p.into_iter().map(|(a, b)| (a, b + l)).collect::<Vec<_>>();

    let res = maximum_matching_of_bipartite_graph(l + r, p);

    writeln!(out, "{}", res.len()).unwrap();
    for (c, d) in res {
        writeln!(out, "{} {}", c, d - l).unwrap();
    }
}
