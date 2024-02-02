// https://judge.yosupo.jp/problem/convolution_mod_large
use convolution::convolution;
use iolib::{putvln, scan};
use montgomery_modint::Mod998244353;

fn main() {
    scan!(n: usize, m: usize, a: [u32; n], b: [u32; m]);

    let c = convolution::<Mod998244353>(a, b);

    putvln!(c, sep = ' ');
}
