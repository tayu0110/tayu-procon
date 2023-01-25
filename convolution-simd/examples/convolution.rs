// https://judge.yosupo.jp/problem/convolution_mod
// https://atcoder.jp/contests/practice2/tasks/practice2_f
use convolution_simd::convolution;
use iolib::scan;
use modint::Mod998244353;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, m: usize, a: [u32; n], b: [u32; m]);

    let c = convolution::<Mod998244353>(a, b);

    write!(out, "{}", c[0]).unwrap();
    for c in c.into_iter().skip(1) {
        write!(out, " {}", c).unwrap();
    }
    writeln!(out, "").unwrap();
}
