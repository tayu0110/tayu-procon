// https://atcoder.jp/contests/atc001/tasks/fft_c
use proconio::{ input, fastout };
use convolution::convolution;
use modint::{ Mint, Mod998244353 };

type Mint998244353 = Mint<Mod998244353>;

#[fastout]
fn main() {
    input! {n: usize};
 
    let mut a = Vec::with_capacity(n);
    let mut b = Vec::with_capacity(n);
    for _ in 0..n {
        input! {na: i64, nb: i64}
        a.push(Mint998244353::raw(na));
        b.push(Mint998244353::raw(nb));
    }
 
    let c = convolution(&a, &b);
    println!("0");
    for res in c {
        println!("{}", res);
    }
}