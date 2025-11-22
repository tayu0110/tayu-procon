use graph::{dijkstra_heap, UnDirectedTree};
use iolib::scan;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, p: [(usize, usize, i64); n - 1]);

    let mut tree = UnDirectedTree::try_from(p).unwrap();
    tree.reroot_with_diameter();

    let root = tree.root();
    let dist = dijkstra_heap(root, &tree);
    let max = dist.iter().max().unwrap();
    let (mut now, _) = dist
        .iter()
        .enumerate()
        .filter(|(_, v)| v == &max)
        .next_back()
        .unwrap();

    let mut res = vec![now];
    while now != root {
        for (to, w) in tree.edges(now) {
            if dist[*to] + *w == dist[now] {
                res.push(*to);
                now = *to;
                break;
            }
        }
    }

    writeln!(out, "{} {}", max, res.len()).unwrap();
    for (i, v) in res.into_iter().rev().enumerate() {
        if i > 0 {
            write!(out, " {}", v).unwrap();
        } else {
            write!(out, "{}", v).unwrap();
        }
    }
    writeln!(out).unwrap();
}
