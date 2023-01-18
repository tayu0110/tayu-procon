// https://judge.yosupo.jp/problem/point_add_range_sum
use iolib::scan;
use segtree::SegmentTree;

fn main() {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut stdout = std::io::BufWriter::new(stdout.lock());

    scan!(n: usize, q: usize, a: [usize; n]);

    let mut st = SegmentTree::from_vec(&a, 0, |l, r| l + r);

    for _ in 0..q {
        scan!(t: usize);
        if t == 0 {
            scan!(p: usize, x: usize);
            st.update_by(p, x, |old, val| old + val);
        } else {
            scan!(l: usize, r: usize);
            writeln!(stdout, "{}", st.foldl(l, r)).unwrap();
        }
    }
}
