#![feature(test)]

extern crate test;

use convolution_simd::common::bit_reverse;
use convolution_simd::cooley_tukey::{cooley_tukey_radix_4_butterfly, cooley_tukey_radix_4_butterfly_inv};
use convolution_simd::fft_cache::FftCache;
use montgomery_modint::{Mod998244353, MontgomeryModint};

type Modint = MontgomeryModint<Mod998244353>;

pub fn ntt_cooley_tukey_radix_4(a: &mut [Modint]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);
    bit_reverse(deg, a);
    let cache = FftCache::<Mod998244353>::new();
    unsafe { cooley_tukey_radix_4_butterfly(deg, log, a, &cache) }
}
pub fn intt_cooley_tukey_radix_4(a: &mut [Modint]) {
    let deg = a.len();
    let log = deg.trailing_zeros() as usize;
    debug_assert_eq!(a.len(), 1 << log);
    bit_reverse(deg, a);
    let cache = FftCache::<Mod998244353>::new();
    unsafe { cooley_tukey_radix_4_butterfly_inv(deg, log, a, &cache) }
    let inv = Modint::new(deg as u32).inv();
    a.iter_mut().for_each(|c| *c *= inv)
}

#[test]
fn cooley_tukey_radix_4_test() {
    for i in 0..=13 {
        let n = 1 << i;
        let data: Vec<Modint> = (1..=n).map(|v| Modint::new(v)).collect();
        let mut data1 = data.clone();
        ntt_cooley_tukey_radix_4(&mut data1);
        intt_cooley_tukey_radix_4(&mut data1);
        assert_eq!(data, data1);
    }
}

use crate::test::Bencher;
#[bench]
fn cooley_tukey_radix_4_bench(b: &mut Bencher) {
    b.iter(|| {
        for i in 15..=20 {
            let n = 1 << i;
            let mut data: Vec<Modint> = (1..=n).map(|v| Modint::new(v)).collect();
            ntt_cooley_tukey_radix_4(&mut data);
            intt_cooley_tukey_radix_4(&mut data);
        }
    })
}
