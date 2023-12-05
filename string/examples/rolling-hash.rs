// https://atcoder.jp/contests/abc284/tasks/abc284_f
use iolib::{putln, scan};
use string::{DynamicRollingHash, RollingHash};

#[allow(unused)]
fn solve_by_fixed_rolling_hash(n: usize, t: &str) {
    let rev_t = t.chars().rev().collect::<String>();

    let rh = RollingHash::new(t);
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

#[allow(unused)]
fn solve_by_dynamic_rolling_hash(n: usize, t: &str) {
    let mut hash = DynamicRollingHash::new(t);

    for i in 0..=n {
        if hash.get(..i) + hash.get(i + n..) == hash.get_reverse(i..i + n) {
            putln!(t[i..i + n].chars().rev().collect::<String>());
            putln!(i);
            return;
        }
    }

    putln!(-1);
}

fn main() {
    scan!(n: usize, t: String);

    // solve_by_fixed_rolling_hash(n, &t);
    solve_by_dynamic_rolling_hash(n, &t);
}
