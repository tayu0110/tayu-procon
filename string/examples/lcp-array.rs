// https://atcoder.jp/contests/practice2/tasks/practice2_i
use iolib::{putln, scan};
use string::SuffixArray;

fn main() {
    scan!(s: String);

    let sa = SuffixArray::new(&s);
    let lcpa = sa.lcp_array();

    putln!(s.len() * (s.len() + 1) / 2 - lcpa.into_iter().sum::<usize>());
}
