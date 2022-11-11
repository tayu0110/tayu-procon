use iolib::scan;
use numeric::factorize;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(q: usize, a: [u64; q]);

    for a in a {
        let mut f = factorize(a);
        f.sort();

        write!(out, "{}", f.len()).unwrap();
        for f in f {
            write!(out, " {}", f).unwrap();
        }
        writeln!(out, "").unwrap();
    }
}
