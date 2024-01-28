// https://judge.yosupo.jp/problem/polynomial_interpolation_on_geometric_sequence
use iolib::*;
use montgomery_modint::{Mod998244353, MontgomeryModint};
use polynomial::Polynomial;

type Modint = MontgomeryModint<Mod998244353>;

fn main() {
    scan!(n: usize, a: u32, r: u32, y: [u32; n]);

    let mut xs = vec![Modint::zero(); n];
    if n > 0 {
        xs[0] = Modint::new(a);
        for i in 1..n {
            xs[i] = xs[i - 1] * Modint::new(r);
        }
    }
    let res: Vec<u32> =
        Polynomial::interpolation(xs, y.into_iter().map(Modint::new).collect()).into();
    putitln!(res.into_iter(), sep = ' ');
}
