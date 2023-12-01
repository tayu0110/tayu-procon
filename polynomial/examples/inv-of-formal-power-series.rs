// https://judge.yosupo.jp/problem/inv_of_formal_power_series
use iolib::{putvsln, scan};
use montgomery_modint::Mod998244353;
use polynomial::Polynomial;

fn main() {
    scan!(n: usize, a: [u32; n]);

    let poly = Polynomial::<Mod998244353>::from(a);
    let inv: Vec<u32> = poly.inv(poly.deg()).into();

    putvsln!(inv);
}
