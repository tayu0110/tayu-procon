// https://atcoder.jp/contests/abc087/tasks/arc090_b
use iolib::{putln, scan};
use unionfind::WeightedUnionFind;

fn main() {
    scan!(n: usize, m: usize, p: [(usize, usize, i64); m]);

    let mut uf = WeightedUnionFind::new(n);

    for (l, r, d) in p {
        let (l, r) = (l - 1, r - 1);
        if uf.merge(l, r, d).is_err() && uf.diff(l, r) != d {
            putln!("No");
            return;
        }
    }

    putln!("Yes");
}
