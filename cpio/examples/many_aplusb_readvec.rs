// https://judge.yosupo.jp/problem/many_aplusb
use cpio::*;

fn main() {
    scan!(t: usize, query: [(u64, u64); t]);

    putln!(query.iter().map(|(a, b)| a + b).collect::<Vec<_>>(), @sep = " ");
}
