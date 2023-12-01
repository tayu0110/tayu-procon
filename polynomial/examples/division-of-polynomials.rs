// https://judge.yosupo.jp/problem/division_of_polynomials
use iolib::{put, putln, putvsln, scan};
use montgomery_modint::Mod998244353;
use polynomial::Polynomial;

fn main() {
    scan!(n: usize, m: usize, f: [u32; n], g: [u32; m]);

    let f = Polynomial::<Mod998244353>::from(f);
    let g = Polynomial::<Mod998244353>::from(g);

    let (q, r) = f.div_rem(g);
    let (q, r): (Vec<u32>, Vec<u32>) = (q.into(), r.into());

    put!(q.len());
    put!(" ");
    putln!(r.len());
    if !q.is_empty() {
        putvsln!(q);
    }

    if !r.is_empty() {
        putvsln!(r);
    }
}
