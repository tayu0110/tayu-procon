// https://atcoder.jp/contests/atc001/tasks/fft_c
use convolution_simd::convolution;
use montgomery_modint::Mod998244353;
use proconio::{fastout, input};

#[fastout]
fn main() {
    input! {n: usize, p: [(u32, u32); n]};

    let (a, b) = p.into_iter().unzip();

    let c = convolution::<Mod998244353>(a, b);
    println!("0");
    for res in c {
        println!("{}", res);
    }
}
