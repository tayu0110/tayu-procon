// https://atcoder.jp/contests/tessoku-book/tasks/tessoku_book_bd
use iolib::{putln, scan};
use string::RollingHash;

fn main() {
    scan!(_n: usize, q: usize, s: String);

    let hash = RollingHash::new(&s);

    for _ in 0..q {
        scan!(a: usize, b: usize, c: usize, d: usize);

        if hash.get(a - 1..b) == hash.get(c - 1..d) {
            putln!("Yes");
        } else {
            putln!("No");
        }
    }
}
