// https://judge.yosupo.jp/problem/exp_of_formal_power_series
use iolib::*;
use montgomery_modint::Mod998244353;
use polynomial::Polynomial;

fn main() {
    scan!(n: usize, a: [u32; n]);

    let poly: Polynomial<Mod998244353> = a.into();
    let res: Vec<u32> = poly.exp(n).unwrap().into();
    putitln!(res.into_iter(), sep = ' ');
}
