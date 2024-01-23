// https://judge.yosupo.jp/problem/sqrt_of_formal_power_series
use iolib::*;
use montgomery_modint::Mod998244353;
use polynomial::Polynomial;

fn main() {
    scan!(n: usize, a: [u32; n]);

    let poly = Polynomial::<Mod998244353>::from(a);
    if let Some(res) = poly.sqrt() {
        let res: Vec<u32> = res.into();
        putitln!(res.into_iter(), sep = ' ');
    } else {
        putln!(-1);
    }
}
