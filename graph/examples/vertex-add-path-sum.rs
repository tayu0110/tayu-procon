// https://judge.yosupo.jp/problem/vertex_add_path_sum
use fenwick_tree::FenwickTree;
use graph::{path_query, UnDirectedTree};
use iolib::{putln, scan};

fn main() {
    scan!(n: usize, q: usize, a: [usize; n], e: [(usize, usize); n - 1]);

    let mut t = vec![vec![]; n];
    for (u, v) in e {
        t[u].push(v);
        t[v].push(u);
    }
    let tree = UnDirectedTree::from(t);
    let (path_query, index) = path_query(&tree);

    let mut ft = FenwickTree::new(n, 0);
    for i in 0..n {
        ft.add(index(i), a[i]);
    }

    for _ in 0..q {
        scan!(t: usize);

        if t == 0 {
            scan!(p: usize, x: usize);
            ft.add(index(p), x);
        } else {
            scan!(u: usize, v: usize);
            let indices = path_query(u, v);

            let mut sum = 0;
            for (u, v) in indices {
                sum += ft.get_sum(u.min(v), u.max(v) + 1);
            }

            putln!(sum);
        }
    }
}
