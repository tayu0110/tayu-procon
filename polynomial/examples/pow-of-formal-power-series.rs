// https://judge.yosupo.jp/problem/pow_of_formal_power_series
use iolib::*;
use montgomery_modint::Mod998244353;
use polynomial::Polynomial;

fn main() {
    scan!(n: usize, m: u64, a: [u32; n]);

    let poly = Polynomial::<Mod998244353>::from(a);
    let res: Vec<u32> = poly.pow(m, n).into();

    putitln!(res.into_iter(), sep = ' ');
}
