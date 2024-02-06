// https://judge.yosupo.jp/problem/kth_term_of_linearly_recurrent_sequence
use iolib::*;
use montgomery_modint::Mod998244353;
use polynomial::kth_term_of_linearly_recurrent_sequence;

fn main() {
    scan!(d: usize, k: u64, a: [u32; d], c: [u32; d]);
    putln!(kth_term_of_linearly_recurrent_sequence::<Mod998244353>(c, a, k).val());
}
