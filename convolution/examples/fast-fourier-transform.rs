// https://atcoder.jp/contests/atc001/tasks/fft_c
use convolution::convolution;
use iolib::{putln, putvln, scan};
use montgomery_modint::Mod998244353;

fn main() {
    scan!(n: usize, p: [(u32, u32); n]);

    let (a, b) = p.into_iter().unzip();

    let c = convolution::<Mod998244353>(a, b);
    putln!(0);
    putvln!(c);
}
