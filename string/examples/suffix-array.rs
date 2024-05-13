// https://judge.yosupo.jp/problem/suffixarray
use iolib::{putitln, scan};
use string::SuffixArray;

fn main() {
    scan!(s: String);

    let sa = SuffixArray::new(&s);

    putitln!(sa.into_iter(), sep = ' ');
}
