// https://judge.yosupo.jp/problem/primitive_root
use cpio::*;
use math::MathInt;

fn main() {
    scan!(q: usize);

    for _ in 0..q {
        scan!(p: u64);
        putln!(p.primitive_root());
    }
}
