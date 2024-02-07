// https://judge.yosupo.jp/problem/find_linear_recurrence
use iolib::*;
use montgomery_modint::{Mod998244353, MontgomeryModint};
use polynomial::berlekamp_massey;

fn main() {
    scan!(n: usize, mut a: [u32; n]);

    let poly = berlekamp_massey::<Mod998244353>(a);
    putln!(poly.deg() - 1);
    let res: Vec<MontgomeryModint<Mod998244353>> = poly.into();
    putitln!(res.into_iter().skip(1).map(|r| (-r).val()), sep = ' ');
}
