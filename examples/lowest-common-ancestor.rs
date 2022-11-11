use iolib::scan;
use graph::{
    UnDirectedTree, lca
};

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, q: usize, p: [usize; n-1], q: [(usize, usize); q]);
    let p = vec![std::usize::MAX].into_iter().chain(p.into_iter()).collect();

    let mut tree = UnDirectedTree::from_par_list(p).unwrap();

    let lca = lca(&mut tree);

    for (u, v) in q {
        writeln!(out, "{}", lca(u, v)).unwrap();
    }
}
