#![feature(test)]

extern crate test;

use convolution_simd::{convolution, convolution_1e97, convolution_mod_2_64, fft_cache::FftCache, intt, ntt};
use montgomery_modint::{Mod4194304001, Mod998244353, MontgomeryModint};

use test::Bencher;
#[bench]
fn simple_ntt_bench(b: &mut Bencher) {
    type Modint = MontgomeryModint<Mod998244353>;
    let cache = FftCache::new();
    b.iter(|| {
        for i in 15..=20 {
            let mut data = (0..1 << i).map(|v| Modint::raw(v)).collect::<Vec<_>>();
            // let data = ntt(data, &cache);
            // let _ = intt(data, &cache);
            ntt(&mut data, &cache);
            intt(&mut data, &cache);
        }
    })
}

#[test]
fn convolution_test() {
    let a = vec![1, 2, 3, 4];
    let b = vec![1, 2, 4, 8];
    let c = convolution::<Mod998244353>(a, b);
    assert_eq!(c, vec![1, 4, 11, 26, 36, 40, 32]);
}

#[test]
fn convolution_large_mod_test() {
    let a = vec![1, 2, 3, 4];
    let b = vec![1, 2, 4, 8];
    let c = convolution::<Mod4194304001>(a, b);
    assert_eq!(c, vec![1, 4, 11, 26, 36, 40, 32]);
}

#[test]
fn convolution_1e97_test() {
    let a = vec![1, 2, 3, 4];
    let b = vec![1, 2, 4, 8];
    let c = convolution_1e97(a, b);
    assert_eq!(c, vec![1, 4, 11, 26, 36, 40, 32]);
}

#[test]
fn convolution_mod_2_64_test() {
    let a = vec![1, 2, 3, 4];
    let b = vec![1, 2, 4, 8];
    let c = convolution_mod_2_64(a, b);
    assert_eq!(c, vec![1, 4, 11, 26, 36, 40, 32]);
}
