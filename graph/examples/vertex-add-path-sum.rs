// https://judge.yosupo.jp/problem/vertex_add_path_sum
use fenwick_tree::FenwickTree;
use graph::{HeavyLightDecomposition, PathVertex};
use iolib::{putln, scan};

fn main() {
    scan!(
        n: usize,
        q: usize,
        a: [usize; n],
        e: [(usize, usize); n - 1]
    );

    let hld = HeavyLightDecomposition::from_edges(n, e);

    let mut ft = FenwickTree::new(n, 0);
    for (i, a) in a.into_iter().enumerate() {
        ft.add(hld.index(i), a);
    }

    for _ in 0..q {
        scan!(t: usize);

        if t == 0 {
            scan!(p: usize, x: usize);
            ft.add(hld.index(p), x);
        } else {
            scan!(u: usize, v: usize);

            let mut sum = 0;
            for path in hld.path_vertex_ranges(u, v) {
                match path {
                    PathVertex::Range { from, to } => {
                        sum += ft.get_sum(from.min(to), from.max(to) + 1);
                    }
                    _ => unreachable!(),
                }
            }

            putln!(sum);
        }
    }
}
