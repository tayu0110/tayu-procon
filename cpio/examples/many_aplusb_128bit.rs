// https://judge.yosupo.jp/problem/many_aplusb_128bit
use cpio::{putln, scan};

fn main() {
    scan!(t: usize);

    for _ in 0..t {
        scan!(a: i128, b: i128);
        putln!(a + b);
    }
}
