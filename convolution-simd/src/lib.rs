mod common;
pub mod cooley_tukey;
mod fft_cache;
pub mod gentleman_sande;

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{_mm256_loadu_si256, _mm256_set1_epi32, _mm256_setzero_si256, _mm256_storeu_si256};
use std::ptr::copy_nonoverlapping;

use common::{_mm256_add_mod_epi32, montgomery_multiplication_u32x8, montgomery_reduction_u32x8};
use cooley_tukey::cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2;
use fft_cache::FftCache;
use gentleman_sande::gentleman_sande_radix_4_butterfly_montgomery_modint_avx2;
use math::{ext_gcd, garner};
use modint::{Mod645922817, Mod754974721, Mod880803841, Mod897581057, Mod998244353, Modulo, MontgomeryModint};

pub fn convolution<M: Modulo>(mut a: Vec<u32>, mut b: Vec<u32>) -> Vec<u32> {
    let deg = a.len() + b.len() - 1;
    let n = deg.next_power_of_two();
    let log = n.trailing_zeros() as usize;

    a.resize(n, 0);
    b.resize(n, 0);

    let modulo = unsafe { _mm256_set1_epi32(M::MOD as i32) };
    let modulo_inv = unsafe { _mm256_set1_epi32(M::MOD_INV as i32) };

    let (mut a, mut b) = if n < 8 {
        (
            a.into_iter().map(|v| MontgomeryModint::<M>::new(v)).collect::<Vec<_>>(),
            b.into_iter().map(|v| MontgomeryModint::<M>::new(v)).collect::<Vec<_>>(),
        )
    } else {
        unsafe {
            let r2 = _mm256_set1_epi32(M::R2 as i32);
            a.chunks_exact_mut(8).for_each(|v| {
                let res = montgomery_multiplication_u32x8(_mm256_loadu_si256(v.as_ptr() as _), r2, modulo, modulo_inv);
                _mm256_storeu_si256(v.as_mut_ptr() as _, res);
            });
            b.chunks_exact_mut(8).for_each(|v| {
                let res = montgomery_multiplication_u32x8(_mm256_loadu_si256(v.as_ptr() as _), r2, modulo, modulo_inv);
                _mm256_storeu_si256(v.as_mut_ptr() as _, res);
            });
            (
                a.into_iter().map(|v| MontgomeryModint::<M>::from_mont_expr(v)).collect::<Vec<_>>(),
                b.into_iter().map(|v| MontgomeryModint::<M>::from_mont_expr(v)).collect::<Vec<_>>(),
            )
        }
    };

    let cache = FftCache::<MontgomeryModint<M>>::new(log);

    unsafe {
        gentleman_sande_radix_4_butterfly_montgomery_modint_avx2(n, log, &mut a, &cache);
        gentleman_sande_radix_4_butterfly_montgomery_modint_avx2(n, log, &mut b, &cache);
    }

    if n < 8 {
        a.iter_mut().zip(b.into_iter()).for_each(|(a, b)| *a *= b);
    } else {
        unsafe {
            for (v, w) in a.chunks_exact_mut(8).zip(b.chunks_exact(8)) {
                let res = montgomery_multiplication_u32x8(_mm256_loadu_si256(v.as_ptr() as _), _mm256_loadu_si256(w.as_ptr() as _), modulo, modulo_inv);
                _mm256_storeu_si256(v.as_mut_ptr() as _, res)
            }
        }
    }

    unsafe {
        cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2(n, log, &mut a, &cache);
    }

    let ninv = MontgomeryModint::<M>::new(n as u32).inv();
    if n < 8 {
        a.iter_mut().take(deg).for_each(|v| *v *= ninv);
        a.into_iter().take(deg).map(|v| v.val()).collect()
    } else {
        unsafe {
            let ninv = _mm256_set1_epi32(ninv.val_mont_expr() as i32);
            for v in a.chunks_exact_mut(8).take((deg + 7) / 8) {
                let res = montgomery_multiplication_u32x8(_mm256_loadu_si256(v.as_ptr() as _), ninv, modulo, modulo_inv);
                _mm256_storeu_si256(v.as_mut_ptr() as _, montgomery_reduction_u32x8(res, modulo, modulo_inv));
            }
            a.into_iter().take(deg).map(|v| v.val_mont_expr()).collect()
        }
    }
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
    let na = a.iter().cloned().map(|a| (a % Mod998244353::MOD as u64) as u32).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| (b % Mod998244353::MOD as u64) as u32).collect::<Vec<_>>();
    let c1 = convolution::<Mod998244353>(na, nb);
    let na = a.iter().cloned().map(|a| (a % Mod897581057::MOD as u64) as u32).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| (b % Mod897581057::MOD as u64) as u32).collect::<Vec<_>>();
    let c2 = convolution::<Mod897581057>(na, nb);
    let na = a.iter().cloned().map(|a| (a % Mod880803841::MOD as u64) as u32).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| (b % Mod880803841::MOD as u64) as u32).collect::<Vec<_>>();
    let c3 = convolution::<Mod880803841>(na, nb);
    let na = a.iter().cloned().map(|a| (a % Mod754974721::MOD as u64) as u32).collect::<Vec<_>>();
    let nb = b.iter().cloned().map(|b| (b % Mod754974721::MOD as u64) as u32).collect::<Vec<_>>();
    let c4 = convolution::<Mod754974721>(na, nb);
    let a = a.into_iter().map(|a| (a % Mod645922817::MOD as u64) as u32).collect::<Vec<_>>();
    let b = b.into_iter().map(|b| (b % Mod645922817::MOD as u64) as u32).collect::<Vec<_>>();
    let c5 = convolution::<Mod645922817>(a, b);

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
    let initialize = |mut a: Vec<u32>| -> Vec<MontgomeryModint<_>> {
        unsafe {
            let r2 = _mm256_set1_epi32(Mod998244353::R2 as i32);
            a.chunks_exact_mut(8).for_each(|v| {
                let res = montgomery_multiplication_u32x8(_mm256_loadu_si256(v.as_ptr() as _), r2, modulo, modulo_inv);
                _mm256_storeu_si256(v.as_mut_ptr() as _, res);
            });
        }
        a.into_iter().map(|v| MontgomeryModint::<Mod998244353>::from_mont_expr(v)).collect::<Vec<_>>()
    };

    a.resize((len_a + 7) / 8 * 8, 0);
    b.resize((len_b + 7) / 8 * 8, 0);
    let a = initialize(a);
    let b = initialize(b);

    let cache = FftCache::<MontgomeryModint<Mod998244353>>::new(width.trailing_zeros() as usize);

    let x = a
        .chunks(width >> 1)
        .map(|a| {
            let mut x = vec![MontgomeryModint::zero(); width];
            unsafe { copy_nonoverlapping(a.as_ptr(), x.as_mut_ptr(), a.len()) }
            unsafe { gentleman_sande_radix_4_butterfly_montgomery_modint_avx2(x.len(), x.len().trailing_zeros() as usize, &mut x, &cache) }
            x
        })
        .collect::<Vec<_>>();
    let y = b
        .chunks(width >> 1)
        .map(|a| {
            let mut x = vec![MontgomeryModint::zero(); width];
            unsafe { copy_nonoverlapping(a.as_ptr(), x.as_mut_ptr(), a.len()) }
            unsafe { gentleman_sande_radix_4_butterfly_montgomery_modint_avx2(x.len(), x.len().trailing_zeros() as usize, &mut x, &cache) }
            x
        })
        .collect::<Vec<_>>();

    let mut res = vec![MontgomeryModint::<Mod998244353>::zero(); std::cmp::max(8, (len_a + len_b - 1).next_power_of_two())];
    let mut p = vec![MontgomeryModint::zero(); width];
    for s in 0..(x.len() + y.len() - 1) {
        for i in 0..=s {
            if let (Some(x), Some(y)) = (x.get(i), y.get(s - i)) {
                for ((p, x), y) in p.chunks_exact_mut(8).zip(x.chunks_exact(8)).zip(y.chunks_exact(8)) {
                    unsafe {
                        _mm256_storeu_si256(
                            p.as_mut_ptr() as _,
                            _mm256_add_mod_epi32(
                                _mm256_loadu_si256(p.as_ptr() as _),
                                montgomery_multiplication_u32x8(_mm256_loadu_si256(x.as_ptr() as _), _mm256_loadu_si256(y.as_ptr() as _), modulo, modulo_inv),
                                modulo,
                            ),
                        );
                    }
                }
            }
        }
        unsafe { cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2(width, width.trailing_zeros() as usize, &mut p, &cache) }
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
        res.into_iter().take(deg).map(|v| v.val_mont_expr()).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::{convolution, convolution_1e97, convolution_mod_2_64};
    use modint::Mod998244353;

    #[test]
    fn convolution_test() {
        let a = vec![1, 2, 3, 4];
        let b = vec![1, 2, 4, 8];
        let c = convolution::<Mod998244353>(a, b);
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
