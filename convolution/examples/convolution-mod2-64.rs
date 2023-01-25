// https://judge.yosupo.jp/problem/convolution_mod_2_64
use convolution::convolution_mod_2_64;
use iolib::scan;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());
    scan!(n: usize, m: usize, a: [u64; n], b: [u64; m]);

    let c = convolution_mod_2_64(a, b);

    write!(out, "{}", c[0]).unwrap();
    for c in c.into_iter().skip(1) {
        write!(out, " {}", c).unwrap();
    }
    writeln!(out, "").unwrap();
}
