// https://judge.yosupo.jp/problem/convolution_mod_1000000007
use convolution::convolution;
use iolib::{putvln, scan};
use montgomery_modint::Mod1000000007;

fn main() {
    scan!(n: usize, m: usize, a: [u32; n], b: [u32; m]);

    let c = convolution::<Mod1000000007>(a, b);

    putvln!(c, sep = ' ');
}
