// https://judge.yosupo.jp/problem/multipoint_evaluation
use iolib::{putvln, scan};
use montgomery_modint::{Mod998244353, MontgomeryModint};
use polynomial::Polynomial;

fn main() {
    scan!(n: usize, m: usize, c: [u32; n], p: [u32; m]);

    let p = p.into_iter().map(MontgomeryModint::raw).collect::<Vec<_>>();
    let f = Polynomial::<Mod998244353>::from(c);

    let res: Polynomial<Mod998244353> = f.multipoint_evaluation(p).into();
    let res: Vec<u32> = res.into();

    putvln!(res, sep = ' ');
}
