// https://judge.yosupo.jp/problem/segment_add_get_min
use cpio::{putln, scan};
use ds::LiChaoTree;

fn main() {
    scan!(n: usize, q: usize);

    let mut lct = LiChaoTree::new(-1_000_000_010..1_000_000_010isize);
    for _ in 0..n {
        scan!(l: isize, r: isize, a: isize, b: isize);
        lct.add_segment((a, b), l..r);
    }

    for _ in 0..q {
        scan!(ty: u8);

        if ty == 0 {
            scan!(l: isize, r: isize, a: isize, b: isize);

            lct.add_segment((a, b), l..r);
        } else {
            scan!(p: isize);

            let res = lct.evaluate(p);
            if res == isize::MAX {
                putln!("INFINITY");
            } else {
                putln!(res);
            }
        }
    }
}
