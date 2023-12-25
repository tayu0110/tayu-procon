// https://judge.yosupo.jp/problem/pow_of_matrix
use iolib::*;
use matrix::Matrix;
use montgomery_modint::{Mod998244353, MontgomeryModint};

fn main() {
    scan!(n: usize, k: u64, a: [[u32; n]; n]);

    let matrix = Matrix::<MontgomeryModint<Mod998244353>>::from(a);
    let res: Vec<Vec<u32>> = matrix.pow(k).into();
    for v in res {
        putitln!(v.into_iter(), sep = ' ');
    }
}
