// https://judge.yosupo.jp/problem/suffixarray
use iolib::scan;
use suffix_array::SuffixArray;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(s: String);

    let sa = SuffixArray::new(&s);

    let sa = sa.get_sa();

    write!(out, "{}", sa[0]).unwrap();
    for sa in sa.into_iter().skip(1) {
        write!(out, " {}", sa).unwrap();
    }
    writeln!(out, "").unwrap();
}
