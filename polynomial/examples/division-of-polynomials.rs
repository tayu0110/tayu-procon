// https://judge.yosupo.jp/problem/division_of_polynomials
use iolib::scan;
use modint::Mod998244353;
use polynomial::Polynomial;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, m: usize, f: [u32; n], g: [u32; m]);

    let f = Polynomial::<Mod998244353>::from(f);
    let g = Polynomial::<Mod998244353>::from(g);

    let (q, r) = f.div_rem(g);
    let (q, r): (Vec<u32>, Vec<u32>) = (q.into(), r.into());

    writeln!(out, "{} {}", q.len(), r.len()).unwrap();
    if !q.is_empty() {
        write!(out, "{}", q[0]).unwrap();
        for q in q.into_iter().skip(1) {
            write!(out, " {}", q).unwrap();
        }
    }
    writeln!(out, "").unwrap();

    if !r.is_empty() {
        write!(out, "{}", r[0]).unwrap();
        for r in r.into_iter().skip(1) {
            write!(out, " {}", r).unwrap();
        }
    }
    writeln!(out, "").unwrap();
}
