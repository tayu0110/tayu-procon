// https://atcoder.jp/contests/abc324/tasks/abc324_c
use iolib::{putln, putvsln, scan};
use string::RollingHash;

fn main() {
    scan!(n: usize, t: String, s: [String; n]);

    let thash = RollingHash::new(&t);

    let mut res = vec![];
    for (i, s) in s.into_iter().enumerate() {
        if s.len() == t.len() {
            if s.chars().zip(t.chars()).filter(|(s, t)| s != t).count() <= 1 {
                res.push(i + 1);
            }
            continue;
        }

        if s.len().abs_diff(t.len()) > 1 {
            continue;
        }

        let shash = RollingHash::new(&s);
        let mut f = false;
        let (s, shash, thash) =
            if s.len() > t.len() { (&s, &shash, &thash) } else { (&t, &thash, &shash) };
        for i in 0..s.len() {
            if i == s.len() - 1 {
                f |= thash.get(..) == shash.get(..i);
            } else {
                f |= thash.get(..) == shash.get(..i) + shash.get(i + 1..);
            }
        }

        if f {
            res.push(i + 1);
        }
    }

    putln!(res.len());
    putvsln!(res);
}
