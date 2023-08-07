pub mod common;
pub mod cooley_tukey;
pub mod fft_cache;
pub mod gentleman_sande;
pub mod traits;

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::_mm256_storeu_si256;

use cooley_tukey::cooley_tukey_radix_4_butterfly_inv;
use fft_cache::FftCache;
use gentleman_sande::gentleman_sande_radix_4_butterfly;
use montgomery_modint::{Mod645922817, Mod754974721, Mod880803841, Mod897581057, Mod998244353, Modulo, MontgomeryModint, MontgomeryModintx8};
use std::ptr::copy_nonoverlapping;
pub use traits::Nttable;

type Modint<M> = MontgomeryModint<M>;
type Modintx8<M> = MontgomeryModintx8<M>;

#[inline]
pub fn ntt<M: Modulo>(a: &mut Vec<Modint<M>>, cache: &FftCache<M>) {
    let n = a.len();
    let log = n.trailing_zeros() as usize;
    assert_eq!(n, 1 << log);

    unsafe { gentleman_sande_radix_4_butterfly(n, log, a, cache) }
}

#[inline]
pub fn intt<M: Modulo>(a: &mut Vec<Modint<M>>, cache: &FftCache<M>) {
    let n = a.len();
    let log = n.trailing_zeros() as usize;
    assert_eq!(n, 1 << log);

    unsafe {
        cooley_tukey_radix_4_butterfly_inv(n, log, a, cache);
        let ninv = Modint::raw(n as u32).inv();
        if n < 8 {
            a.iter_mut().for_each(|a| *a *= ninv);
        } else {
            let ninv = Modintx8::<M>::splat(ninv);
            a.chunks_exact_mut(8).for_each(|v| (Modintx8::load(v.as_ptr()) * ninv).store(v.as_mut_ptr()));
        }
    }
}

#[inline]
pub fn dot<M: Modulo>(a: &mut Vec<Modint<M>>, b: &[Modint<M>]) {
    if a.len() < 8 {
        a.iter_mut().zip(b).for_each(|(a, &b)| *a *= b);
    } else {
        unsafe {
            a.chunks_exact_mut(8)
                .zip(b.chunks_exact(8))
                .for_each(|(v, w)| (Modintx8::load(v.as_ptr()) * Modintx8::load(w.as_ptr())).store(v.as_mut_ptr()))
        }
    }
}

pub fn convolution<M: Modulo>(mut a: Vec<u32>, mut b: Vec<u32>) -> Vec<u32> {
    let deg = a.len() + b.len() - 1;
    let n = deg.next_power_of_two();

    a.resize(n, 0);
    b.resize(n, 0);

    let cache = FftCache::<M>::new();

    a.ntt_with_cache(&cache);
    b.ntt_with_cache(&cache);

    Nttable::<M>::dot_assign(&mut a, &b);

    a.intt_with_cache(&cache);
    a.resize(deg, 0);
    a
}

pub fn convolution_1e97(a: Vec<u32>, b: Vec<u32>) -> Vec<u32> {
    let c1 = convolution::<Mod880803841>(a.clone(), b.clone());
    let c2 = convolution::<Mod897581057>(a.clone(), b.clone());
    let c3 = convolution::<Mod998244353>(a, b);

    const MOD: u64 = 1000_000_007;
    const P: [u64; 3] = [Mod880803841::N as u64, Mod897581057::N as u64, Mod998244353::N as u64];
    const P1P2: u64 = P[0] * P[1] % P[2];
    const P1P2MOD: u64 = P[0] * P[1] % MOD;
    let p1i = Modint::<Mod897581057>::raw(P[0] as u32).inv().val() as u64;
    let p2i = Modint::<Mod998244353>::raw(P1P2 as u32).inv().val() as u64;
    c1.into_iter()
        .zip(c2.into_iter().zip(c3.into_iter()))
        .map(|(c1, (c2, c3))| {
            let t1 = (c2 as u64 + P[1] - c1 as u64) * p1i % P[1];
            let res2 = (c1 as u64 + t1 * P[0]) % P[2];
            let res3 = (c1 as u64 + t1 * P[0]) % MOD;
            let t2 = (c3 as u64 + P[2] - res2) * p2i % P[2];
            ((res3 + t2 * P1P2MOD) % MOD) as u32
        })
        .collect()
}

pub fn convolution_mod_2_64(a: Vec<u64>, b: Vec<u64>) -> Vec<u64> {
    let c1 = convolution::<Mod645922817>(
        a.iter().cloned().map(|a| (a % Mod645922817::N as u64) as u32).collect(),
        b.iter().cloned().map(|b| (b % Mod645922817::N as u64) as u32).collect(),
    );
    let c2 = convolution::<Mod754974721>(
        a.iter().cloned().map(|a| (a % Mod754974721::N as u64) as u32).collect(),
        b.iter().cloned().map(|b| (b % Mod754974721::N as u64) as u32).collect(),
    );
    let c3 = convolution::<Mod880803841>(
        a.iter().cloned().map(|a| (a % Mod880803841::N as u64) as u32).collect(),
        b.iter().cloned().map(|b| (b % Mod880803841::N as u64) as u32).collect(),
    );
    let c4 = convolution::<Mod897581057>(
        a.iter().cloned().map(|a| (a % Mod897581057::N as u64) as u32).collect(),
        b.iter().cloned().map(|b| (b % Mod897581057::N as u64) as u32).collect(),
    );
    let c5 = convolution::<Mod998244353>(
        a.into_iter().map(|a| (a % Mod998244353::N as u64) as u32).collect(),
        b.into_iter().map(|b| (b % Mod998244353::N as u64) as u32).collect(),
    );

    const P: [u64; 5] = [Mod645922817::N as u64, Mod754974721::N as u64, Mod880803841::N as u64, Mod897581057::N as u64, Mod998244353::N as u64];
    const PROD01: u64 = (P[0] as u64).wrapping_mul(P[1]);
    const PROD012: u64 = PROD01.wrapping_mul(P[2]);
    const PROD0123: u64 = PROD012.wrapping_mul(P[3]);
    const P0P1: u64 = P[0] * P[1] % P[2];
    const P0P1P2: u64 = P[0] * P[1] % P[3] * P[2] % P[3];
    const P0P1P2P3: u64 = P[0] * P[1] % P[4] * P[2] % P[4] * P[3] % P[4];
    let pi = vec![
        Modint::<Mod754974721>::raw(P[0] as u32).inv().val() as u64,
        Modint::<Mod880803841>::from(P0P1).inv().val() as u64,
        Modint::<Mod897581057>::from(P0P1P2).inv().val() as u64,
        Modint::<Mod998244353>::from(P0P1P2P3).inv().val() as u64,
    ];
    let mut res = vec![];
    for i in 0..c1.len() {
        let t0 = c1[i] as u64;
        let mut w = vec![t0; 5];
        let mut prod = vec![P[0]; 5];
        for (j, c) in vec![c2[i], c3[i], c4[i], c5[i]].into_iter().enumerate() {
            let t = ((c + P[j + 1] as u32 - w[j + 1] as u32) as u64 * pi[j]) % P[j + 1];
            for (k, &p) in P.iter().enumerate().skip(j + 2) {
                w[k] = (w[k] + (t * prod[k])) % p;
                prod[k] = (prod[k] * P[j + 1]) % p;
            }
            w[j] = t;
        }

        res.push(
            t0.wrapping_add(w[0].wrapping_mul(Mod645922817::N as u64))
                .wrapping_add(w[1].wrapping_mul(PROD01))
                .wrapping_add(w[2].wrapping_mul(PROD012))
                .wrapping_add(w[3].wrapping_mul(PROD0123)),
        )
    }
    res
}

// reference: https://judge.yosupo.jp/submission/68990
pub fn convolution_large(mut a: Vec<u32>, mut b: Vec<u32>) -> Vec<u32> {
    const THRESHOLD: usize = 1 << 23;
    let deg = a.len() + b.len() - 1;
    if deg <= THRESHOLD {
        return convolution::<Mod998244353>(a, b);
    }
    let n = deg.next_power_of_two();
    let width = THRESHOLD >> 1;
    a.resize((a.len() + 7) >> 3 << 3, 0);
    b.resize((b.len() + 7) >> 3 << 3, 0);

    let cache = FftCache::<Mod998244353>::new();

    let x = a
        .chunks(width)
        .map(|a| {
            let mut x = vec![0u32; THRESHOLD];
            unsafe { copy_nonoverlapping(a.as_ptr(), x.as_mut_ptr(), a.len()) }
            x.ntt_with_cache(&cache);
            x
        })
        .collect::<Vec<_>>();
    let y = b
        .chunks(width)
        .map(|a| {
            let mut x = vec![0u32; THRESHOLD];
            unsafe { copy_nonoverlapping(a.as_ptr(), x.as_mut_ptr(), a.len()) }
            x.ntt_with_cache(&cache);
            x
        })
        .collect::<Vec<_>>();

    let mut res = vec![Modint::<Mod998244353>::zero(); n];
    let mut p = vec![Modint::zero(); THRESHOLD];
    for s in 0..(x.len() + y.len() - 1) {
        for i in 0..=s {
            if let (Some(x), Some(y)) = (x.get(i), y.get(s - i)) {
                p.iter_mut().zip(Nttable::<Mod998244353>::dot(x.clone(), &y)).for_each(|(p, v)| *p += Modint::from_rawval(v));
            }
        }
        unsafe {
            cooley_tukey_radix_4_butterfly_inv(THRESHOLD, THRESHOLD.trailing_zeros() as usize, &mut p, &cache);
            for (res, p) in res[(s * width)..].chunks_exact_mut(8).zip(p.chunks_exact_mut(8)) {
                (Modintx8::load(res.as_ptr()) + Modintx8::load(p.as_ptr())).store(res.as_mut_ptr());
                Modintx8::zero().store(p.as_mut_ptr())
            }
        }
    }

    unsafe {
        let ninv = Modintx8::splat(Modint::<Mod998244353>::new(THRESHOLD as u32).inv());
        for v in res.chunks_exact_mut(8).take((deg + 7) >> 3) {
            let res = Modintx8::load(v.as_ptr()) * ninv;
            _mm256_storeu_si256(v.as_mut_ptr() as _, res.val());
        }
        res.into_iter().take(deg).map(|v| v.val).collect()
    }
}
