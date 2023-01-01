// https://judge.yosupo.jp/problem/manhattanmst
use graph::manhattan_minimum_spanning_tree;
use iolib::scan;
use unionfind::UnionFind;

fn main() {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut stdout = std::io::BufWriter::new(stdout.lock());

    scan!(n: usize, p: [(i64, i64); n]);

    let mut uf = UnionFind::new(n);
    let edges = manhattan_minimum_spanning_tree(&p);
    let mut res = vec![];
    let mut res_weight = 0;
    for (w, i, j) in edges {
        if !uf.is_same(i, j) {
            res.push((i, j));
            res_weight += w;
            uf.merge(i, j);
        }
    }

    writeln!(stdout, "{}", res_weight).unwrap();
    for (u, v) in res {
        writeln!(stdout, "{} {}", u, v).unwrap();
    }
}
