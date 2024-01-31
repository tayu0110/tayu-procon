// https://judge.yosupo.jp/problem/polynomial_taylor_shift
use iolib::*;
use montgomery_modint::Mod998244353;
use polynomial::Polynomial;

fn main() {
    scan!(n: usize, c: u32, a: [u32; n]);

    let res: Vec<u32> = Polynomial::<Mod998244353>::from(a)
        .taylor_shift(c.into())
        .into();
    putitln!(res.into_iter(), sep = ' ');
}
