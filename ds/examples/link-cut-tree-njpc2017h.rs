// https://atcoder.jp/contests/njpc2017/tasks/njpc2017_h
use ds::NoOpLinkCutTree;
use iolib::{putln, scan};

fn main() {
    scan!(n: usize, p: [usize; n - 1], c: [u8; n], q: usize);

    let mut lct = NoOpLinkCutTree::new(n);
    for (i, &p) in p.iter().enumerate() {
        if c[i + 1] != c[p - 1] {
            lct.link(p - 1, i + 1).unwrap();
        }
    }

    let mut p = p;
    p.insert(0, 0);

    for _ in 0..q {
        scan!(ty: u8);

        if ty == 1 {
            scan!(u: usize);

            if u != 1 {
                if lct.is_connected(u - 1, p[u - 1] - 1) {
                    lct.cut(u - 1);
                } else {
                    lct.link(p[u - 1] - 1, u - 1).unwrap();
                }
            }
        } else {
            scan!(u: usize, v: usize);

            if lct.is_connected(u - 1, v - 1) {
                putln!("YES");
            } else {
                putln!("NO");
            }
        }
    }
}
