// https://judge.yosupo.jp/problem/polynomial_interpolation
use iolib::{putvln, scan};
use montgomery_modint::Mod998244353;
use polynomial::Polynomial;

fn main() {
    scan!(n: usize, x: [u32; n], y: [u32; n]);

    let x: Polynomial<Mod998244353> = x.into();
    let y: Polynomial<Mod998244353> = y.into();

    let res: Vec<u32> = Polynomial::interpolation(x.into(), y.into()).into();
    putvln!(res, sep = ' ');
}
