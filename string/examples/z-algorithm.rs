// https://judge.yosupo.jp/problem/zalgorithm
use iolib::{putvln, scan};
use string::zalgorithm;

fn main() {
    scan!(s: String);

    putvln!(zalgorithm(s), sep = ' ');
}
