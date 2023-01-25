// https://judge.yosupo.jp/problem/convolution_mod
// https://atcoder.jp/contests/practice2/tasks/practice2_f
use convolution::convolution;
use iolib::scan;
use modint::{Mod998244353, MontgomeryModint};

type Modint = MontgomeryModint<Mod998244353>;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, m: usize);

    let mut a = vec![Modint::zero(); n];
    let mut b = vec![Modint::zero(); m];
    for i in 0..n {
        scan!(na: u32);
        a[i] = Modint::raw(na);
    }
    for i in 0..m {
        scan!(nb: u32);
        b[i] = Modint::raw(nb);
    }

    let c = convolution(a, b);

    write!(out, "{}", c[0]).unwrap();
    for c in c.into_iter().skip(1) {
        write!(out, " {}", c).unwrap();
    }
    writeln!(out, "").unwrap();
}
