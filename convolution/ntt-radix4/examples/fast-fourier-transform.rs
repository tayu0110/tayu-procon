// https://atcoder.jp/contests/atc001/tasks/fft_c
use montgomery_modint::{Mod998244353, MontgomeryModint};
use ntt_radix4::convolution;
use proconio::{fastout, input};

type Mint998244353 = MontgomeryModint<Mod998244353>;

#[fastout]
fn main() {
    input! {n: usize, p: [(Mint998244353, Mint998244353); n]};

    let (a, b) = p.into_iter().unzip();

    let c = convolution(a, b);
    println!("0");
    for res in c {
        println!("{}", res);
    }
}
