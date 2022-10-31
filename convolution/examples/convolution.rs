use iolib::scan;
use convolution::convolution;
use modint::{
    Mint, Mod998244353
};

type Modint = Mint<Mod998244353>;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, m: usize, a: [i64; n], b: [i64; m]);

    let a = a.into_iter().map(|a| Modint::raw(a)).collect::<Vec<_>>();
    let b = b.into_iter().map(|b| Modint::raw(b)).collect::<Vec<_>>();

    let c = convolution(&a, &b);

    write!(out, "{}", c[0]).unwrap();
    for c in c.into_iter().skip(1) {
        write!(out, " {}", c).unwrap();
    }
    writeln!(out, "").unwrap();
}