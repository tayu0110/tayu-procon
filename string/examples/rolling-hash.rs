// https://atcoder.jp/contests/abc284/tasks/abc284_f
use iolib::{putln, scan};
use string::RollingHash;

fn main() {
    scan!(n: usize, t: String);

    let rev_t = t.chars().rev().collect::<String>();

    let rh = RollingHash::new(&t);
    let rev_rh = RollingHash::new(&rev_t);

    for i in 0..=n {
        let sf_hash = rh.get(..i);
        let sb_hash = rh.get(i + n..2 * n);

        let tf_hash = rev_rh.get(n - i..n);
        let tb_hash = rev_rh.get(n..2 * n - i);

        if tf_hash == sf_hash && tb_hash == sb_hash {
            putln!(rev_t.chars().skip(n - i).take(n).collect::<String>());
            putln!(i);
            return;
        }
    }

    putln!(-1);
}
