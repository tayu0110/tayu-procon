// https://atcoder.jp/contests/abc331/tasks/abc331_f
use iolib::{putln, scan};
use string::DynamicRollingHash;

fn main() {
    scan!(n: usize, q: usize, s: String);

    let mut hash = DynamicRollingHash::new(&s);
    let mut rev = DynamicRollingHash::new(&s.chars().rev().collect::<String>());

    for _ in 0..q {
        scan!(ty: u8);

        if ty == 1 {
            scan!(x: usize, c: char);
            hash.set(x - 1, c);
            rev.set(n - x, c);
        } else {
            scan!(l: usize, r: usize);
            let l = l - 1;

            if hash.get(l..r) == rev.get(n - r..n - l) {
                putln!("Yes");
            } else {
                putln!("No");
            }
        }
    }
}
