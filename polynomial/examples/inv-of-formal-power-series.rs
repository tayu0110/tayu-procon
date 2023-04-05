// https://judge.yosupo.jp/problem/inv_of_formal_power_series
use iolib::scan;
use montgomery_modint::Mod998244353;
use polynomial::Polynomial;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, a: [u32; n]);

    let poly = Polynomial::<Mod998244353>::from(a);
    let inv: Vec<u32> = poly.inv(poly.deg()).into();

    write!(out, "{}", inv[0]).unwrap();
    for inv in inv.into_iter().skip(1) {
        write!(out, " {}", inv).unwrap();
    }
    writeln!(out, "").unwrap();
}
