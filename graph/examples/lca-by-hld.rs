use graph::HeavyLightDecomposition;
use iolib::{putln, scan};

fn main() {
    scan!(n: usize, q: usize, p: [usize; n - 1]);

    let hld =
        HeavyLightDecomposition::from_edges(n, p.into_iter().enumerate().map(|(i, v)| (i + 1, v)));
    for _ in 0..q {
        scan!(u: usize, v: usize);

        putln!(hld.lca(u, v));
    }
}
