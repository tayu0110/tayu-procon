// https://judge.yosupo.jp/problem/convolution_mod
use convolution::convolution;
use iolib::scan;
use modint::{Mod998244353, MontgomeryModint};

type Modint = MontgomeryModint<Mod998244353<u32>, u32>;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, m: usize, a: [u32; n], b: [u32; m]);

    let a = a.into_iter().map(|a| Modint::new(a)).collect::<Vec<_>>();
    let b = b.into_iter().map(|b| Modint::new(b)).collect::<Vec<_>>();

    let c = convolution(a, b);

    write!(out, "{}", c[0]).unwrap();
    for c in c.into_iter().skip(1) {
        write!(out, " {}", c).unwrap();
    }
    writeln!(out, "").unwrap();
}
