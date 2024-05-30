// https://judge.yosupo.jp/problem/counting_primes
use cpio::*;
use math::MathInt;

fn main() {
    scan!(n: u64);
    putln!(n.count_primes());
}
