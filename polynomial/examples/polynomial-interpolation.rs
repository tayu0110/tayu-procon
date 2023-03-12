// https://judge.yosupo.jp/problem/polynomial_interpolation
use iolib::scan;
use modint::{Mod998244353, MontgomeryModint};
use polynomial::lagrange_interpolation;

type Modint = MontgomeryModint<Mod998244353>;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, x: [Modint; n], y: [Modint; n]);

    let res: Vec<u32> = lagrange_interpolation(x, y).into();

    write!(out, "{}", res[0]).unwrap();
    for res in res.into_iter().skip(1) {
        write!(out, " {}", res).unwrap();
    }
    writeln!(out, "").unwrap();
}
