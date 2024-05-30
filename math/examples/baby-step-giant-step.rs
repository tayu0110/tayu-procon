// https://atcoder.jp/contests/abc270/tasks/abc270_g
use cpio::*;
use math::{baby_step_giant_step, MathInt};

fn main() {
    scan!(t: usize);

    for _ in 0..t {
        scan!(p: i64, a: i64, b: i64, s: i64, g: i64);

        if a == 0 {
            if g == s {
                putln!("0");
            } else if g == b {
                putln!("1");
            } else {
                putln!("-1");
            }
            continue;
        }

        let mut ap = vec![];
        let mut now = 1;
        let m = (p as f64).sqrt().ceil() as i64 + 1;
        for _ in 0..=m {
            ap.push(now);
            now = now * a % p;
        }

        let mut ab = vec![];
        let mut now = 0;
        for _ in 0..=m {
            ab.push(now);
            now = now * a + b;
            now %= p;
        }

        let mut inv = vec![];
        let mut now = 1;
        for _ in 0..=m {
            let i = now.inverse_mod(p).expect("inverse_mod is not found");
            inv.push(i);
            now = now * a % p;
        }

        let f = |x: i64, exp: i64| -> i64 { (ap[exp as usize] * x + ab[exp as usize]) % p };
        let f_inv = |x: i64, exp: i64| -> i64 {
            ((x - ab[exp as usize]).rem_euclid(p) * inv[exp as usize]).rem_euclid(p)
        };

        assert_eq!(f(s, 0), s);
        assert_eq!(f_inv(s, 0), s);

        if let Some(res) = baby_step_giant_step(s, g, p, f, f_inv) {
            putln!(res);
        } else {
            putln!("-1");
        }
    }
}
