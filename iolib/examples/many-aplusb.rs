// https://judge.yosupo.jp/problem/many_aplusb
use iolib::{putln, scan};

fn main() {
    scan!(t: usize);

    for _ in 0..t {
        scan!(a: usize, b: usize);
        putln!(a + b);
    }
}
