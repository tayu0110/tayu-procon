// https://judge.yosupo.jp/problem/multipoint_evaluation
use iolib::scan;
use modint::{Mod998244353, MontgomeryModint};
use polynomial::Polynomial;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, m: usize, c: [u32; n], p: [u32; m]);

    let p = p.into_iter().map(|v| MontgomeryModint::raw(v)).collect::<Vec<_>>();
    let f = Polynomial::<Mod998244353>::from(c);

    let res = f.multipoint_evaluation(p);

    write!(out, "{}", res[0]).unwrap();
    for r in res.into_iter().skip(1) {
        write!(out, " {}", r).unwrap();
    }
    writeln!(out, "").unwrap();
}
