// https://judge.yosupo.jp/problem/factorize
use iolib::{putitln, putln, scan};
use math::factorize;

fn main() {
    scan!(q: usize, a: [u64; q]);

    for a in a {
        let mut f = factorize(a);
        f.sort_unstable();

        putln!(f.len());
        putitln!(f.into_iter(), sep = ' ');
    }
}
