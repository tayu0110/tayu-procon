
// https://judge.yosupo.jp/problem/suffixarray
use suffix_array::SuffixArray;

fn main() {
    use std::io::BufRead;
    let stdin = std::io::stdin();
    let mut stdin = std::io::BufReader::new(stdin.lock());
    let mut s = String::new();
    stdin.read_line(&mut s).unwrap();
    s.pop();

    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    let sa = SuffixArray::new(&s);

    let sa = sa.get_sa();

    write!(out, "{}", sa[0]).unwrap();
    for sa in sa.into_iter().skip(1) {
        write!(out, " {}", sa).unwrap();
    }
    writeln!(out, "").unwrap();
}
