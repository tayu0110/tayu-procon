// https://onlinejudge.u-aizu.ac.jp/problems/2983
use iolib::scan;
use matrix::{Matrix, Rank};
use montgomery_modint::{Mod1000000007, MontgomeryModint};
use simple_rand::{gen_seed, xor_shift};

type Modint = MontgomeryModint<Mod1000000007>;

fn main() {
    scan!(n: usize, m: usize);

    let mut v = vec![vec![]; n];
    for i in 0..m {
        scan!(k: usize, p: [usize; k]);
        for p in p {
            v[p - 1].push(i);
        }
    }

    let mut res = 0;
    let mut set = std::collections::HashSet::new();
    let mut xs = xor_shift(gen_seed());
    let mut mat = Matrix::zeros(m, m);
    let mut t = vec![];
    for v in v {
        if v.is_empty() {
            res += 1;
        } else if v.len() == 1 {
            set.insert(v[0]);
        } else {
            t.push((std::cmp::min(v[0], v[1]), std::cmp::max(v[0], v[1])));
        }
    }

    res += set.len();

    t.sort();
    t.dedup();

    for (l, r) in t {
        if !set.contains(&l) && !set.contains(&r) {
            let x = Modint::from(xs.next().unwrap());
            mat.set(l, r, x);
            mat.set(r, l, Modint::zero() - x);
        }
    }

    let rank = mat.rank();
    res += rank / 2;

    assert_eq!(rank % 2, 0);

    println!("{}", res);
}
