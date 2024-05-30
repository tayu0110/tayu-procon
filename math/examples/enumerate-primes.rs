// https://judge.yosupo.jp/problem/enumerate_primes
use cpio::*;
use math::CompactSieve;

fn main() {
    scan!(n: usize, a: usize, b: usize);

    let sieve = CompactSieve::new(n + 1);

    let mut pi = 0;
    let mut res = vec![];
    for (i, p) in sieve.primes().take_while(|&p| p <= n).enumerate() {
        pi += 1;
        if i % a == b {
            res.push(p);
        }
    }

    putln!(pi, res.len(), @sep = " ");
    putln!(res, @sep = " ");
}
