// https://judge.yosupo.jp/problem/line_add_get_min
use iolib::{putln, scan};
use segtree::LiChaoTree;

fn main() {
    scan!(n: usize, q: usize);

    let mut lct = LiChaoTree::new(-1_000_000_010..1_000_000_010isize);
    for _ in 0..n {
        scan!(a: isize, b: isize);
        lct.add_line((a, b));
    }

    for _ in 0..q {
        scan!(ty: u8);

        if ty == 0 {
            scan!(a: isize, b: isize);
            lct.add_line((a, b));
        } else {
            scan!(p: isize);

            putln!(lct.evaluate(p));
        }
    }
}
