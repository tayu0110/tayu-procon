// https://judge.yosupo.jp/problem/primality_test
use iolib::{putln, scan};
use math::miller_rabin_test;

fn main() {
    scan!(q: u32);

    for _ in 0..q {
        scan!(n: u64);
        putln!(if miller_rabin_test(n) { "Yes" } else { "No" });
    }
}
