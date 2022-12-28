// https://atcoder.jp/contests/atc001/tasks/fft_c
use convolution::convolution;
use modint::{Mod998244353, MontgomeryModint};
use proconio::{fastout, input};

type Mint998244353 = MontgomeryModint<Mod998244353>;

#[fastout]
fn main() {
    input! {n: usize, a: [Mint998244353; n], b: [Mint998244353; n]};

    let c = convolution(a, b);
    println!("0");
    for res in c {
        println!("{}", res);
    }
}
