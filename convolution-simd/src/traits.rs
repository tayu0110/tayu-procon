use std::arch::x86_64::_mm256_loadu_si256;
use std::arch::x86_64::_mm256_set1_epi32;
use std::arch::x86_64::_mm256_storeu_si256;

use montgomery_modint::{Modulo, MontgomeryModint};

use crate::common::montgomery_multiplication_u32x8;

use super::cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2;
use super::gentleman_sande_radix_4_butterfly_montgomery_modint_avx2;

use super::fft_cache::FftCache;
use super::{dot, intt, ntt};

pub trait Nttable<M: Modulo> {
    fn ntt(self) -> Self;
    fn intt(self) -> Self;
    fn ntt_with_cache(self, cache: &FftCache<MontgomeryModint<M>>) -> Self;
    fn intt_with_cache(self, cache: &FftCache<MontgomeryModint<M>>) -> Self;
    fn dot(self, rhs: &Self) -> Self;
}

impl<M: Modulo> Nttable<M> for Vec<u32> {
    fn ntt(self) -> Self {
        let len = self.len();
        assert_eq!(1 << len.trailing_zeros(), len);
        let cache = FftCache::<MontgomeryModint<M>>::new(len.trailing_zeros() as usize);
        self.ntt_with_cache(&cache)
    }
    fn intt(self) -> Self {
        let len = self.len();
        assert_eq!(1 << len.trailing_zeros(), len);
        let cache = FftCache::<MontgomeryModint<M>>::new(len.trailing_zeros() as usize);
        self.intt_with_cache(&cache)
    }
    fn ntt_with_cache(self, cache: &FftCache<MontgomeryModint<M>>) -> Self {
        assert_eq!(self.len(), cache.twiddle_factors().len() - 1);
        ntt(self, &cache)
    }
    fn intt_with_cache(self, cache: &FftCache<MontgomeryModint<M>>) -> Self {
        assert_eq!(self.len(), cache.twiddle_factors().len() - 1);
        intt(self, &cache)
    }
    fn dot(self, rhs: &Self) -> Self { dot::<M>(self, &rhs) }
}

impl<M: Modulo> Nttable<M> for Vec<MontgomeryModint<M>> {
    fn ntt(self) -> Self {
        let len = self.len();
        assert_eq!(1 << len.trailing_zeros(), len);
        let cache = FftCache::<MontgomeryModint<M>>::new(len.trailing_zeros() as usize);
        self.ntt_with_cache(&cache)
    }
    fn intt(self) -> Self {
        let len = self.len();
        assert_eq!(1 << len.trailing_zeros(), len);
        let cache = FftCache::<MontgomeryModint<M>>::new(len.trailing_zeros() as usize);
        self.intt_with_cache(&cache)
    }
    fn ntt_with_cache(mut self, cache: &FftCache<MontgomeryModint<M>>) -> Self {
        let len = self.len();
        assert_eq!(len, cache.twiddle_factors().len() - 1);
        if len == 1 {
            self
        } else if len == 2 {
            let (c0, c1) = (self[0], self[1]);
            vec![(c0 + c1), (c0 - c1)]
        } else if len == 4 {
            let im = cache.prim_root(2);
            let (c0, c1, c2, c3) = (self[0], self[1], self[2], self[3]);
            let (c0, c1, c2, c3) = {
                let c0pc2 = c0 + c2;
                let c0mc2 = c0 - c2;
                let c1pc3 = c1 + c3;
                let c1mc3 = c1 - c3;
                let c1mc3im = c1mc3 * im;
                (c0pc2 + c1pc3, c0mc2 + c1mc3im, c0pc2 - c1pc3, c0mc2 - c1mc3im)
            };
            vec![c0, c2, c1, c3]
        } else {
            unsafe { gentleman_sande_radix_4_butterfly_montgomery_modint_avx2(len, len.trailing_zeros() as usize, &mut self, &cache) }
            self
        }
    }
    fn intt_with_cache(mut self, cache: &FftCache<MontgomeryModint<M>>) -> Self {
        let len = self.len();
        assert_eq!(len, cache.twiddle_factors().len() - 1);
        if len == 1 {
            self
        } else if len == 2 {
            let (c0, c1) = (self[0], self[1]);
            let div2 = MontgomeryModint::raw(2).inv();
            vec![(c0 + c1) * div2, (c0 - c1) * div2]
        } else if len == 4 {
            let im = FftCache::<MontgomeryModint<M>>::new(2).prim_root_inv(2);
            let (c0, c1, c2, c3) = (self[0], self[1], self[2], self[3]);
            let (c0, c1, c2, c3) = {
                let c0pc2 = c0 + c2;
                let c0mc2 = c0 - c2;
                let c1pc3 = c1 + c3;
                let c1mc3 = c1 - c3;
                let c1mc3im = c1mc3 * im;
                (c0pc2 + c1pc3, c0mc2 + c1mc3im, c0pc2 - c1pc3, c0mc2 - c1mc3im)
            };
            let div4 = MontgomeryModint::raw(4).inv();
            vec![c0 * div4, c2 * div4, c1 * div4, c3 * div4]
        } else {
            unsafe {
                let modulo = _mm256_set1_epi32(M::MOD as i32);
                let modulo_inv = _mm256_set1_epi32(M::MOD_INV as i32);
                cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2(len, len.trailing_zeros() as usize, &mut self, &cache);
                let ninv = _mm256_set1_epi32(MontgomeryModint::<M>::new(len as u32).inv().val as i32);
                for v in self.chunks_exact_mut(8) {
                    let res = montgomery_multiplication_u32x8(_mm256_loadu_si256(v.as_ptr() as _), ninv, modulo, modulo_inv);
                    _mm256_storeu_si256(v.as_mut_ptr() as _, res);
                }
            }
            self
        }
    }
    fn dot(self, rhs: &Self) -> Self {
        dot::<M>(self.into_iter().map(|v| v.val).collect(), &rhs.into_iter().map(|v| v.val).collect::<Vec<_>>())
            .into_iter()
            .map(|v| MontgomeryModint::from_mont_expr(v))
            .collect()
    }
}
