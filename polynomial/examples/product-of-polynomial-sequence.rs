// https://judge.yosupo.jp/problem/product_of_polynomial_sequence
use iolib::*;
use montgomery_modint::{Mod998244353, MontgomeryModint};
use polynomial::Polynomial;

type Modint = MontgomeryModint<Mod998244353>;

fn solve(l: usize, r: usize) -> Polynomial<Mod998244353> {
    let len = r - l;
    if len == 0 {
        Polynomial::from(vec![Modint::one()])
    } else if len == 1 {
        scan!(d: usize, a: [u32; d + 1]);
        Polynomial::from(a)
    } else {
        let m = (r + l) >> 1;
        solve(l, m) * solve(m, r)
    }
}

fn main() {
    scan!(n: usize);
    let res: Vec<u32> = solve(0, n).into();
    putitln!(res.into_iter(), sep = ' ');
}
