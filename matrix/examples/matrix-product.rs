// https://judge.yosupo.jp/problem/matrix_product
use iolib::{put, putln, scan};
use matrix::Matrix;
use montgomery_modint::{Mod998244353, MontgomeryModint};

type Modint = MontgomeryModint<Mod998244353>;

fn main() {
    scan!(
        n: usize,
        m: usize,
        k: usize,
        a: [[u32; m]; n],
        b: [[u32; k]; m]
    );

    let a = Matrix::<Modint>::from(a);
    let b = Matrix::<Modint>::from(b);

    let c = a * b;

    for i in 0..n {
        put!(c[(i, 0)].val());
        for j in 1..k {
            put!(" ");
            put!(c[(i, j)].val());
        }
        putln!();
    }
}
