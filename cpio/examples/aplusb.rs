// https://judge.yosupo.jp/problem/aplusb
use cpio::{putln, scan};

fn main() {
    scan!(mut a: u32, b: u32);
    a += b;
    putln!(a);
}
