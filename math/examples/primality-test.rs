// https://judge.yosupo.jp/problem/primality_test
use cpio::*;
use math::MathInt;

fn main() {
    scan!(q: u32);

    for _ in 0..q {
        scan!(n: u64);
        putln!(if n.is_prime() { "Yes" } else { "No" });
    }
}
