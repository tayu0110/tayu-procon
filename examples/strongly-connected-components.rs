use iolib::scan;
use graph::{
    DirectedGraph, scc
};

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, m: usize, p: [(usize, usize); m]);

    let graph = DirectedGraph::from_edges(n, p);
    let scc = scc(&graph);

    writeln!(out, "{}", scc.len()).unwrap();
    for res in scc {
        write!(out, "{}", res.len()).unwrap();
        for v in res {
            write!(out, " {}", v).unwrap();
        }
        writeln!(out, "").unwrap();
    }
}
