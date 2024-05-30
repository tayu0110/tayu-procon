// https://judge.yosupo.jp/problem/sqrt_mod
use cpio::*;
use math::MathInt;

fn main() {
    scan!(t: usize);

    for _ in 0..t {
        scan!(y: u32, p: u32);

        if let Some(res) = y.sqrt_mod(p) {
            putln!(res);
        } else {
            putln!(-1);
        }
    }
}
