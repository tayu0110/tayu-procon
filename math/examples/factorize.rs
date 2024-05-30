// https://judge.yosupo.jp/problem/factorize
use cpio::*;
use math::MathInt;

fn main() {
    scan!(q: usize, a: [u64; q]);

    for a in a {
        let mut f = a
            .factorize()
            .flat_map(|(f, c)| (0..c).map(move |_| f))
            .collect::<Vec<_>>();
        f.sort_unstable();

        putln!(f.len(), f, @sep = " ");
    }
}
