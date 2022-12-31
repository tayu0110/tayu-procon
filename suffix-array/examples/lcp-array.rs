// https://atcoder.jp/contests/practice2/tasks/practice2_i
use proconio::input;
use suffix_array::SuffixArray;

fn main() {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut stdout = std::io::BufWriter::new(stdout.lock());

    input! {s: String}

    let sa = SuffixArray::new(&s);
    let lcpa = sa.lcp_array();

    writeln!(stdout, "{}", s.len() * (s.len() + 1) / 2 - lcpa.into_iter().sum::<usize>()).unwrap();
}
