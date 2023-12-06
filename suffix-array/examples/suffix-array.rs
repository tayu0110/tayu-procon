// https://judge.yosupo.jp/problem/suffixarray
use iolib::{putitln, scan};
use suffix_array::SuffixArray;

fn main() {
    scan!(s: String);

    let sa = SuffixArray::new(&s);

    putitln!(sa.into_iter(), sep = ' ');
}
