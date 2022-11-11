// https://atcoder.jp/contests/atc001/tasks/fft_c
use proconio::{ input, fastout };
use convolution::fconvolution;

#[fastout]
fn main() {
    input! {n: usize};
 
    let mut a = Vec::with_capacity(n);
    let mut b = Vec::with_capacity(n);
    for _ in 0..n {
        input! {na: f64, nb: f64}
        a.push(na);
        b.push(nb);
    }
 
    let c = fconvolution(&a, &b);
    println!("0");
    for res in c {
        println!("{}", res.round());
    }
}