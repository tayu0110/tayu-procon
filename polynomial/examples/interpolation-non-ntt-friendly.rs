// https://atcoder.jp/contests/arc033/tasks/arc033_4
use iolib::*;
use montgomery_modint::{Mod1000000007, MontgomeryModint};
use polynomial::Polynomial;

type Modint = MontgomeryModint<Mod1000000007>;

fn main() {
    scan!(n: usize, a: [u32; n + 1], t: u32);

    let poly = Polynomial::<Mod1000000007>::interpolation(
        (0..=n as u32).map(Modint::new).collect(),
        a.into_iter().map(Modint::new).collect(),
    );

    println!("{}", poly.evaluate(t.into()));
}
