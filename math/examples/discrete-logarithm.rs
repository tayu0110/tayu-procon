// https://judge.yosupo.jp/problem/discrete_logarithm_mod
use cpio::*;
use math::MathInt;

fn main() {
    scan!(t: usize);

    for _ in 0..t {
        scan!(x: u32, y: u32, m: u32);

        if let Some(res) = y.log_mod(x, m) {
            putln!(res);
        } else {
            putln!(-1);
        }
    }
}
