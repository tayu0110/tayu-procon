// https://judge.yosupo.jp/problem/suffixarray
use iolib::{put, putln, scan};
use suffix_array::SuffixArray;

fn main() {
    scan!(s: String);

    let sa = SuffixArray::new(&s);

    put!(sa[0]);
    for sa in sa.into_iter().skip(1) {
        put!(" ");
        put!(sa);
    }
    putln!();
}
