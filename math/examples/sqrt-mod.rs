// https://judge.yosupo.jp/problem/sqrt_mod
use iolib::{putln, scan};
use math::tonelli_shanks_unchecked;

fn main() {
    scan!(t: usize);

    for _ in 0..t {
        scan!(y: u64, p: u64);

        if let Some(res) = tonelli_shanks_unchecked(y, p) {
            putln!(res);
        } else {
            putln!(-1);
        }
    }
}
