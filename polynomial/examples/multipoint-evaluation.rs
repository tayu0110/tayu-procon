// https://judge.yosupo.jp/problem/multipoint_evaluation
use iolib::{putvln, scan};
use montgomery_modint::{Mod998244353, MontgomeryModint};
use polynomial::Polynomial;

fn main() {
    scan!(n: usize, m: usize, c: [u32; n], p: [u32; m]);

    let p: Vec<MontgomeryModint<Mod998244353>> = Polynomial::<Mod998244353>::from(p).into();
    let res: Vec<u32> =
        Polynomial::from(Polynomial::<Mod998244353>::from(c).multipoint_evaluation(p)).into();

    putvln!(res, sep = ' ');
}
