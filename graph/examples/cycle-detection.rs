use graph::{cycle_detect, DirectedGraph};
use iolib::scan;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, m: usize, p: [(usize, usize); m]);

    let map = p
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, v)| (v, i))
        .collect::<std::collections::HashMap<(_, _), _>>();

    let graph = DirectedGraph::from_edges(n, p);

    if let Some(cycle) = cycle_detect(&graph) {
        writeln!(out, "{}", cycle.len()).unwrap();
        for i in 0..cycle.len() {
            writeln!(
                out,
                "{}",
                map.get(&(cycle[i], cycle[(i + 1) % cycle.len()])).unwrap()
            )
            .unwrap();
        }
    } else {
        writeln!(out, "-1").unwrap();
    }
}
