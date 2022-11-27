// https://atcoder.jp/contests/atc001/tasks/fft_c
use convolution::convolution;
use modint::{Mod998244353, MontgomeryModint};
use proconio::{fastout, input};

type Mint998244353 = MontgomeryModint<Mod998244353<u32>, u32>;

#[fastout]
fn main() {
    input! {n: usize};

    let mut a = Vec::with_capacity(n);
    let mut b = Vec::with_capacity(n);
    for _ in 0..n {
        input! {na: u32, nb: u32}
        a.push(Mint998244353::new(na));
        b.push(Mint998244353::new(nb));
    }

    let c = convolution(a, b);
    println!("0");
    for res in c {
        println!("{}", res);
    }
}
