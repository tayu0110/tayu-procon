#![feature(test)]

extern crate test;

use montgomery_modint::{Mod998244353, MontgomeryModint};

use number_theoretic_transform::NumberTheoreticTransform;
use test::Bencher;
#[bench]
fn simple_ntt_bench(b: &mut Bencher) {
    type Modint = MontgomeryModint<Mod998244353>;
    b.iter(|| {
        for i in 15..=20 {
            let mut data = (0..1 << i).map(Modint::raw).collect::<Vec<_>>();
            data.ntt();
            data.intt();
        }
    })
}
