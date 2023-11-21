// https://judge.yosupo.jp/problem/zalgorithm
use iolib::{putvec_with_spaceln, scan};
use string::zalgorithm;

fn main() {
    scan!(s: String);

    putvec_with_spaceln!(zalgorithm(s));
}
