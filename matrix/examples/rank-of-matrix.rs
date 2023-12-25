use iolib::*;
use matrix::{Matrix, Rank};
use montgomery_modint::{Mod998244353, MontgomeryModint};

type Modint = MontgomeryModint<Mod998244353>;

fn main() {
    scan!(n: usize, m: usize, a: [[u32; m]; n]);

    let matrix = Matrix::<Modint>::from(a);
    putln!(matrix.rank());
}
