#![feature(test)]

extern crate test;

use convolution_simd::common::bit_reverse;
use convolution_simd::fft_cache::FftCache;
use convolution_simd::gentleman_sande::gentleman_sande_radix_4_butterfly;
#[cfg(test)]
use convolution_simd::gentleman_sande::gentleman_sande_radix_4_butterfly_inv;
use montgomery_modint::{Mod998244353, MontgomeryModint};

type Modint = MontgomeryModint<Mod998244353>;

pub fn ntt_gentleman_sande_radix_4(a: &mut [Modint]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);
    let cache = FftCache::new();
    unsafe { gentleman_sande_radix_4_butterfly(deg, log, a, &cache) }
    bit_reverse(deg, a);
}

pub fn intt_gentleman_sande_radix_4(a: &mut [Modint]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);
    let cache = FftCache::new();
    unsafe { gentleman_sande_radix_4_butterfly_inv(deg, log, a, &cache) }
    bit_reverse(deg, a);
    let inv = Modint::new(deg as u32).inv();
    a.iter_mut().for_each(|c| *c *= inv)
}

#[test]
fn gentleman_sande_radix_4_test() {
    for i in 0..=13 {
        let n = 1 << i;
        let data: Vec<Modint> = (1..=n).map(|v| Modint::new(v)).collect();
        let mut data1 = data.clone();
        ntt_gentleman_sande_radix_4(&mut data1);
        intt_gentleman_sande_radix_4(&mut data1);
        assert_eq!(data, data1);
    }
}

use crate::test::Bencher;
#[bench]
fn gentleman_sande_radix_4_bench(b: &mut Bencher) {
    b.iter(|| {
        for i in 15..=20 {
            let n = 1 << i;
            let mut data: Vec<Modint> = (1..=n).map(|v| Modint::new(v)).collect();
            ntt_gentleman_sande_radix_4(&mut data);
            intt_gentleman_sande_radix_4(&mut data);
        }
    })
}
