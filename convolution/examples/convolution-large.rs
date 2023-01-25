// https://judge.yosupo.jp/problem/convolution_mod_large
use convolution::convolution_998_upper223;
use iolib::scan;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, m: usize, a: [u32; n], b: [u32; m]);

    let c = convolution_998_upper223(a, b);

    write!(out, "{}", c[0]).unwrap();
    for c in c.into_iter().skip(1) {
        write!(out, " {}", c).unwrap();
    }
    writeln!(out, "").unwrap();
}
