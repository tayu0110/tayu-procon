use graph::{dijkstra_heap, DirectedGraph};
use iolib::scan;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(
        n: usize,
        m: usize,
        s: usize,
        t: usize,
        p: [(usize, usize, i64); m]
    );

    let graph = DirectedGraph::from_weighted_edges(n, p);

    let dist = dijkstra_heap(s, &graph);

    if dist[t] == i64::MAX {
        writeln!(out, "-1").unwrap();
        return;
    }

    let mut now = t;
    let mut res = vec![t];
    let mut reached = vec![false; n];
    let rgraph = graph.rev_graph();
    while now != s {
        reached[now] = true;
        for (to, w) in rgraph.edges(now) {
            if dist[*to] + *w == dist[now] && !reached[*to] {
                res.push(*to);
                now = *to;
                break;
            }
        }
    }

    res.reverse();
    writeln!(out, "{} {}", dist[t], res.len() - 1).unwrap();
    for v in res.windows(2) {
        writeln!(out, "{} {}", v[0], v[1]).unwrap();
    }
}
