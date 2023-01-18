// https://judge.yosupo.jp/problem/point_add_range_sum
use fenwick_tree::FenwickTree;
use iolib::scan;

fn main() {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut stdout = std::io::BufWriter::new(stdout.lock());

    scan!(n: usize, q: usize, a: [usize; n]);

    let mut ft = FenwickTree::new(n, 0);
    for (i, a) in a.into_iter().enumerate() {
        ft.add(i, a);
    }

    for _ in 0..q {
        scan!(t: usize);

        if t == 0 {
            scan!(p: usize, x: usize);
            ft.add(p, x);
        } else {
            scan!(l: usize, r: usize);
            writeln!(stdout, "{}", ft.get_sum(l, r)).unwrap();
        }
    }
}
