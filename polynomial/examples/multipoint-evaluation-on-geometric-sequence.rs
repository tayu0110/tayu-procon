// https://judge.yosupo.jp/problem/multipoint_evaluation_on_geometric_sequence
use iolib::*;
use montgomery_modint::{Mod998244353, MontgomeryModint};
use polynomial::Polynomial;

type Modint = MontgomeryModint<Mod998244353>;

fn main() {
    scan!(n: usize, m: usize, a: u32, r: u32, c: [u32; n]);

    let mut xs = vec![Modint::zero(); m];
    if n > 0 {
        xs[0] = Modint::new(a);
        for i in 1..m {
            xs[i] = xs[i - 1] * Modint::new(r);
        }
    }

    let res: Vec<u32> =
        Polynomial::from(Polynomial::<Mod998244353>::from(c).multipoint_evaluation(xs)).into();
    putitln!(res.into_iter(), sep = ' ');
}
