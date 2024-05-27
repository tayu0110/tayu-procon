// https://judge.yosupo.jp/problem/many_aplusb
use cpio::{putln, scan};

fn main() {
    scan!(t: usize);

    for _ in 0..t {
        scan!(a: u64, b: u64);
        putln!(a + b);
    }
}
