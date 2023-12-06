use arbitrary_modint::ArbitraryModint;
use iolib::scan;
use matrix::{Determinant, Matrix};

fn main() {
    scan!(n: usize, m: u32, a: [u32; n * n]);
    ArbitraryModint::set_modulo(m);

    let a = a.into_iter().map(ArbitraryModint::raw).collect();
    let res = Matrix::from_vec_as_shape(n, n, a).determinant();

    println!("{res}");
}
