#![feature(test)]

extern crate test;

pub mod common;
pub mod cooley_tukey;
pub mod fft_cache;
pub mod gentleman_sande;
pub mod traits;

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{_mm256_loadu_si256, _mm256_set1_epi32, _mm256_setzero_si256, _mm256_storeu_si256};

use common::{_mm256_add_mod_epi32, montgomery_multiplication_u32x8, montgomery_reduction_u32x8};
use cooley_tukey::cooley_tukey_radix_4_butterfly;
use fft_cache::FftCache;
use gentleman_sande::gentleman_sande_radix_4_butterfly_inv;
use math::{ext_gcd, garner};
use montgomery_modint::{Mod645922817, Mod754974721, Mod880803841, Mod897581057, Mod998244353, Modulo, MontgomeryModint};
use std::ptr::copy_nonoverlapping;
pub use traits::Nttable;

type Modint<M> = MontgomeryModint<M>;

#[inline]
pub fn ntt<M: Modulo>(mut a: Vec<Modint<M>>, cache: &FftCache<M>) -> Vec<Modint<M>> {
    let n = a.len();
    let log = n.trailing_zeros() as usize;
    assert_eq!(n, 1 << log);

    unsafe { cooley_tukey_radix_4_butterfly(n, log, &mut a, cache) }
    a
}

#[inline]
pub fn intt<M: Modulo>(mut a: Vec<Modint<M>>, cache: &FftCache<M>) -> Vec<Modint<M>> {
    let n = a.len();
    let log = n.trailing_zeros() as usize;
    assert_eq!(n, 1 << log);

    unsafe {
        gentleman_sande_radix_4_butterfly_inv(n, log, &mut a, cache);
        let ninv = Modint::raw(n as u32).inv();
        if n < 8 {
            a.iter_mut().for_each(|a| *a *= ninv);
        } else {
            let ninv = _mm256_set1_epi32(ninv.val as i32);
            let modulo = _mm256_set1_epi32(M::MOD as i32);
            let modulo_inv = _mm256_set1_epi32(M::MOD_INV as i32);
            a.chunks_exact_mut(8)
                .for_each(|v| _mm256_storeu_si256(v.as_mut_ptr() as _, montgomery_multiplication_u32x8(_mm256_loadu_si256(v.as_ptr() as _), ninv, modulo, modulo_inv)));
        }
    }
    a
}

#[inline]
pub fn dot<M: Modulo>(mut a: Vec<Modint<M>>, b: &[Modint<M>]) -> Vec<Modint<M>> {
    if a.len() < 8 {
        a.iter_mut().zip(b).for_each(|(a, &b)| *a *= b);
    } else {
        unsafe {
            let modulo = _mm256_set1_epi32(M::MOD as i32);
            let modulo_inv = _mm256_set1_epi32(M::MOD_INV as i32);
            for (v, w) in a.chunks_exact_mut(8).zip(b.chunks_exact(8)) {
                let (a, b) = (_mm256_loadu_si256(v.as_ptr() as _), _mm256_loadu_si256(w.as_ptr() as _));
                _mm256_storeu_si256(v.as_mut_ptr() as _, montgomery_multiplication_u32x8(a, b, modulo, modulo_inv));
            }
        }
    }
    a
}

pub fn convolution<M: Modulo>(mut a: Vec<u32>, mut b: Vec<u32>) -> Vec<u32> {
    let deg = a.len() + b.len() - 1;
    let n = std::cmp::max(8, deg.next_power_of_two());

    a.resize(n, 0);
    b.resize(n, 0);

    let cache = FftCache::<M>::new();

    let a = a.ntt_with_cache(&cache);
    let b = b.ntt_with_cache(&cache);

    let a = <Vec<u32> as Nttable<M>>::dot(a, &b);

    let c = a.intt_with_cache(&cache);
    c.into_iter().take(deg).collect()
}

pub fn convolution_1e97(a: Vec<u32>, b: Vec<u32>) -> Vec<u32> {
    let c1 = convolution::<Mod998244353>(a.clone(), b.clone());
    let c2 = convolution::<Mod897581057>(a.clone(), b.clone());
    let c3 = convolution::<Mod880803841>(a, b);

    const MOD: i64 = 1000_000_007;
    const P: [i64; 3] = [Mod998244353::MOD as i64, Mod897581057::MOD as i64, Mod880803841::MOD as i64];
    c1.into_iter()
        .zip(c2.into_iter().zip(c3.into_iter()))
        .map(|(c1, (c2, c3))| garner(&[c1 as i64, c2 as i64, c3 as i64], &P, MOD).0 as u32)
        .collect()
}

pub fn convolution_mod_2_64(a: Vec<u64>, b: Vec<u64>) -> Vec<u64> {
    let c1 = convolution::<Mod998244353>(
        a.iter().cloned().map(|a| (a % Mod998244353::MOD as u64) as u32).collect(),
        b.iter().cloned().map(|b| (b % Mod998244353::MOD as u64) as u32).collect(),
    );
    let c2 = convolution::<Mod897581057>(
        a.iter().cloned().map(|a| (a % Mod897581057::MOD as u64) as u32).collect(),
        b.iter().cloned().map(|b| (b % Mod897581057::MOD as u64) as u32).collect(),
    );
    let c3 = convolution::<Mod880803841>(
        a.iter().cloned().map(|a| (a % Mod880803841::MOD as u64) as u32).collect(),
        b.iter().cloned().map(|b| (b % Mod880803841::MOD as u64) as u32).collect(),
    );
    let c4 = convolution::<Mod754974721>(
        a.iter().cloned().map(|a| (a % Mod754974721::MOD as u64) as u32).collect(),
        b.iter().cloned().map(|b| (b % Mod754974721::MOD as u64) as u32).collect(),
    );
    let c5 = convolution::<Mod645922817>(
        a.into_iter().map(|a| (a % Mod645922817::MOD as u64) as u32).collect(),
        b.into_iter().map(|b| (b % Mod645922817::MOD as u64) as u32).collect(),
    );

    const P: [u64; 5] = [
        Mod998244353::MOD as u64,
        Mod897581057::MOD as u64,
        Mod880803841::MOD as u64,
        Mod754974721::MOD as u64,
        Mod645922817::MOD as u64,
    ];
    let mut res = vec![];
    for i in 0..c1.len() {
        let mut prod = vec![1; 6];
        let mut w = vec![0; 6];
        for (j, (a, &m)) in vec![c1[i], c2[i], c3[i], c4[i], c5[i]].iter().map(|&v| v as u64).zip(P.iter()).enumerate() {
            let a = a % m;
            let (_, inv, _) = ext_gcd(prod[j] as i64, m as i64);
            let t = ((a as i64 - w[j] as i64) * inv).rem_euclid(m as i64);
            for (k, &p) in P.iter().enumerate().skip(j + 1) {
                w[k] = (w[k] + (t as u64 * prod[k])) % p;
                prod[k] = (prod[k] * m) % p;
            }
            w[5] = (w[5] as u128 + (t as u128 * prod[5] as u128)) as u64;
            prod[5] = (prod[5] as u128 * m as u128) as u64;
        }
        res.push(w[5])
    }
    res
}

// reference: https://judge.yosupo.jp/submission/68990
pub fn convolution_large(mut a: Vec<u32>, mut b: Vec<u32>) -> Vec<u32> {
    const THRESHOLD: usize = 1 << 23;
    let (len_a, len_b) = (a.len(), b.len());
    let width = std::cmp::max(8, std::cmp::min((len_a + len_b - 1).next_power_of_two(), THRESHOLD >> 1)) << 1;

    let modulo = unsafe { _mm256_set1_epi32(Mod998244353::MOD as i32) };
    let modulo_inv = unsafe { _mm256_set1_epi32(Mod998244353::MOD_INV as i32) };

    a.resize((len_a + 7) / 8 * 8, 0);
    b.resize((len_b + 7) / 8 * 8, 0);

    let cache = FftCache::<Mod998244353>::new();

    let x = a
        .chunks(width >> 1)
        .map(|a| {
            let mut x = vec![0u32; width];
            unsafe { copy_nonoverlapping(a.as_ptr(), x.as_mut_ptr(), a.len()) }
            x.ntt_with_cache(&cache)
        })
        .collect::<Vec<_>>();
    let y = b
        .chunks(width >> 1)
        .map(|a| {
            let mut x = vec![0u32; width];
            unsafe { copy_nonoverlapping(a.as_ptr(), x.as_mut_ptr(), a.len()) }
            x.ntt_with_cache(&cache)
        })
        .collect::<Vec<_>>();

    let mut res = vec![MontgomeryModint::<Mod998244353>::zero(); std::cmp::max(8, (len_a + len_b - 1).next_power_of_two())];
    let mut p = vec![MontgomeryModint::zero(); width];
    for s in 0..(x.len() + y.len() - 1) {
        for i in 0..=s {
            if let (Some(x), Some(y)) = (x.get(i), y.get(s - i)) {
                p.iter_mut().zip(Nttable::<Mod998244353>::dot(x.clone(), &y)).for_each(|(p, v)| *p += Modint::raw(v));
            }
        }
        unsafe { gentleman_sande_radix_4_butterfly_inv(width, width.trailing_zeros() as usize, &mut p, &cache) }
        for (res, p) in res[(s * width / 2)..].chunks_exact_mut(8).zip(p.chunks_exact_mut(8)) {
            unsafe {
                _mm256_storeu_si256(
                    res.as_mut_ptr() as _,
                    _mm256_add_mod_epi32(_mm256_loadu_si256(res.as_ptr() as _), _mm256_loadu_si256(p.as_ptr() as _), modulo),
                );
                _mm256_storeu_si256(p.as_mut_ptr() as _, _mm256_setzero_si256())
            }
        }
    }

    unsafe {
        let deg = len_a + len_b - 1;
        let ninv = MontgomeryModint::<Mod998244353>::new(width as u32).inv();
        let ninv = _mm256_set1_epi32(ninv.val_mont_expr() as i32);
        for v in res.chunks_exact_mut(8).take((deg + 7) / 8) {
            let res = montgomery_multiplication_u32x8(_mm256_loadu_si256(v.as_ptr() as _), ninv, modulo, modulo_inv);
            _mm256_storeu_si256(v.as_mut_ptr() as _, montgomery_reduction_u32x8(res, modulo, modulo_inv));
        }
        res.into_iter().take(deg).map(|v| v.val).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::{convolution, convolution_1e97, convolution_mod_2_64};
    use montgomery_modint::{Mod4194304001, Mod998244353};

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
}
