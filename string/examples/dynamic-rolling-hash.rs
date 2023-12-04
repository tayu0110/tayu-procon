// https://atcoder.jp/contests/abc331/tasks/abc331_f
use iolib::{putln, scan};
use string::DynamicRollingHash;

fn main() {
    scan!(_: usize, q: usize, s: String);

    let mut hash = DynamicRollingHash::new(&s);

    for _ in 0..q {
        scan!(ty: u8);

        if ty == 1 {
            scan!(x: usize, c: char);
            hash.set(x - 1, c);
        } else {
            scan!(l: usize, r: usize);
            let l = l - 1;

            if hash.is_palindrome(l..r) {
                putln!("Yes");
            } else {
                putln!("No");
            }
        }
    }
}
