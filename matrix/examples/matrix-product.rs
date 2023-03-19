// https://judge.yosupo.jp/problem/matrix_product
use iolib::scan;
use matrix::Matrix;
use static_modint::{Mod998244353, StaticModint};

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, m: usize, k: usize, a: [[u32; m]; n], b: [[u32; k]; m]);

    let a = Matrix::<StaticModint<Mod998244353>>::from(a);
    let b = Matrix::<StaticModint<Mod998244353>>::from(b);

    let c = a.mul(&b);

    for i in 0..n {
        write!(out, "{}", c.get(i, 0)).unwrap();
        for j in 1..k {
            write!(out, " {}", c.get(i, j)).unwrap();
        }
        writeln!(out, "").unwrap();
    }
}
