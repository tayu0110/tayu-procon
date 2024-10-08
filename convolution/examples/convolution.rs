// https://judge.yosupo.jp/problem/convolution_mod
// https://atcoder.jp/contests/practice2/tasks/practice2_f
use convolution::convolution;
use cpio::*;
use montgomery_modint::Mod998244353;

fn main() {
    scan!(n: usize, m: usize, a: [u32; n], b: [u32; m]);

    let c = convolution::<Mod998244353>(a, b);

    putln!(c, @sep = " ");
}
