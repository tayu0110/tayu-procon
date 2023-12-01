// https://judge.yosupo.jp/problem/zalgorithm
use iolib::{putvsln, scan};
use string::zalgorithm;

fn main() {
    scan!(s: String);

    putvsln!(zalgorithm(s));
}
