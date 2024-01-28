// https://atcoder.jp/contests/arc033/tasks/arc033_4
use iolib::*;
use montgomery_modint::{Mod1000000007, MontgomeryModint};
use polynomial::interpolation_with_eval;

type Modint = MontgomeryModint<Mod1000000007>;

fn main() {
    scan!(n: usize, a: [u32; n + 1], t: u32);

    putln!(interpolation_with_eval(a.into_iter().map(Modint::new).collect(), Modint::new(t)).val());
}
