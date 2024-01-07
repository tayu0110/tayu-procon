// https://judge.yosupo.jp/problem/primitive_root
use iolib::*;
use math::primitive_root;

fn main() {
    scan!(q: usize);

    for _ in 0..q {
        scan!(p: u64);
        putln!(primitive_root(p));
    }
}
