// https://judge.yosupo.jp/problem/polynomial_interpolation
use iolib::{putvec_with_spaceln, scan};
use montgomery_modint::{Mod998244353, MontgomeryModint};
use polynomial::Polynomial;

type Modint = MontgomeryModint<Mod998244353>;

fn main() {
    scan!(n: usize, x: [Modint; n], y: [Modint; n]);

    let res: Vec<u32> = Polynomial::interpolation(x, y).into();
    putvec_with_spaceln!(res);
}
