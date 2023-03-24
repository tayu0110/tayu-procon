// https://judge.yosupo.jp/problem/vertex_add_path_sum
use graph::{path_query, UnDirectedTree};
use iolib::{putln, scan};
use segtree::SegmentTree;

fn main() {
    scan!(n: usize, q: usize, a: [usize; n], e: [(usize, usize); n - 1]);

    let mut t = vec![vec![]; n];
    for (u, v) in e {
        t[u].push(v);
        t[v].push(u);
    }
    let tree = UnDirectedTree::try_from(t).unwrap();
    let path_query = path_query(&tree);

    let a = {
        let mut na = vec![0; n];
        for i in 0..n {
            na[path_query(i, i)[0].0] = a[i];
        }
        na
    };

    let mut st = SegmentTree::from_vec(&a, 0, |l, r| l + r);

    for _ in 0..q {
        scan!(t: usize);

        if t == 0 {
            scan!(p: usize, x: usize);
            let index = path_query(p, p)[0].0;
            st.update_by(index, x, |l, r| l + r);
        } else {
            scan!(u: usize, v: usize);
            let indices = path_query(u, v);

            let mut sum = 0;
            for (u, v) in indices {
                sum += st.foldl(u.min(v), u.max(v) + 1);
            }

            putln!(sum);
        }
    }
}
