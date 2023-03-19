// https://judge.yosupo.jp/problem/matrix_det
use iolib::scan;
use matrix::Matrix;
use montgomery_modint::{Mod998244353, MontgomeryModint};

fn main() {
    scan!(n: usize, a: [[u32; n]; n]);

    let mat = Matrix::<MontgomeryModint<Mod998244353>>::from(a);

    println!("{}", mat.determinant());
}
