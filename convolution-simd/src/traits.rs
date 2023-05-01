// use crate::cooley_tukey::cooley_tukey_radix_4_butterfly;
// use crate::gentleman_sande::gentleman_sande_radix_4_butterfly_inv;

use super::fft_cache::FftCache;
use super::{dot, intt, ntt};
use montgomery_modint::{Modulo, MontgomeryModint, MontgomeryModintx8};
use std::arch::x86_64::_mm256_storeu_si256;
use std::mem::transmute;

pub trait Nttable<M: Modulo> {
    fn ntt(&mut self);
    fn intt(&mut self);
    fn ntt_with_cache(&mut self, cache: &FftCache<M>);
    fn intt_with_cache(&mut self, cache: &FftCache<M>);
    fn dot(self, rhs: &Self) -> Self;
    fn dot_assign(&mut self, rhs: &Self);
}

impl<M: Modulo> Nttable<M> for Vec<MontgomeryModint<M>> {
    fn ntt(&mut self) {
        let len = self.len();
        assert_eq!(1 << len.trailing_zeros(), len);
        let cache = FftCache::new();
        self.ntt_with_cache(&cache)
    }
    fn intt(&mut self) {
        let len = self.len();
        assert_eq!(1 << len.trailing_zeros(), len);
        let cache = FftCache::new();
        self.intt_with_cache(&cache)
    }
    fn ntt_with_cache(&mut self, cache: &FftCache<M>) { ntt(self, &cache) }
    fn intt_with_cache(&mut self, cache: &FftCache<M>) { intt(self, &cache) }
    fn dot(self, rhs: &Self) -> Self { dot::<M>(self, &rhs) }
    fn dot_assign(&mut self, rhs: &Self) {
        if self.len() < 8 {
            self.iter_mut().zip(rhs).for_each(|(a, &b)| *a *= b);
        } else {
            unsafe {
                self.chunks_exact_mut(8)
                    .zip(rhs.chunks_exact(8))
                    .for_each(|(v, w)| (MontgomeryModintx8::load_ptr(v.as_ptr()) * MontgomeryModintx8::load_ptr(w.as_ptr())).store_ptr(v.as_mut_ptr()))
            }
        }
    }
}

impl<M: Modulo> Nttable<M> for Vec<u32> {
    fn ntt(&mut self) {
        let len = self.len();
        assert_eq!(1 << len.trailing_zeros(), len);
        let cache = FftCache::<M>::new();
        self.ntt_with_cache(&cache)
    }
    fn intt(&mut self) {
        let len = self.len();
        assert_eq!(1 << len.trailing_zeros(), len);
        let cache = FftCache::<M>::new();
        self.intt_with_cache(&cache)
    }
    fn ntt_with_cache(&mut self, cache: &FftCache<M>) {
        convert_u32_to_modint::<M>(self);
        unsafe { transmute::<_, &mut Vec<MontgomeryModint<M>>>(self).ntt_with_cache(cache) }
    }
    fn intt_with_cache(&mut self, cache: &FftCache<M>) {
        let a = unsafe { transmute::<_, &mut Vec<MontgomeryModint<M>>>(self) };
        a.intt_with_cache(cache);
        convert_modint_to_u32::<M>(a);
    }
    fn dot(self, rhs: &Self) -> Self { unsafe { transmute(transmute::<_, Vec<MontgomeryModint<M>>>(self).dot(transmute(rhs))) } }
    fn dot_assign(&mut self, rhs: &Self) {
        let a = unsafe { transmute::<_, &mut Vec<MontgomeryModint<M>>>(self) };
        let b = unsafe { transmute::<_, &Vec<MontgomeryModint<M>>>(rhs) };
        a.dot_assign(b);
    }
}

#[inline]
fn convert_u32_to_modint<M: Modulo>(a: &mut Vec<u32>) {
    if a.len() < 8 {
        a.iter_mut().for_each(|a| *a = MontgomeryModint::<M>::from(*a).val);
    } else {
        unsafe {
            a.chunks_exact_mut(8)
                .for_each(|v| (MontgomeryModintx8::<M>::load_ptr(v.as_ptr() as _) * MontgomeryModintx8::from_rawval(M::R2X8)).store_ptr(v.as_mut_ptr() as _));
        }
    }
}

#[inline]
fn convert_modint_to_u32<M: Modulo>(a: &mut Vec<MontgomeryModint<M>>) {
    if a.len() < 8 {
        a.iter_mut().for_each(|a| *a = MontgomeryModint::from_mont_expr(a.val()));
    } else {
        unsafe {
            a.chunks_exact_mut(8)
                .for_each(|v| _mm256_storeu_si256(v.as_mut_ptr() as _, MontgomeryModintx8::<M>::load_ptr(v.as_ptr()).val()))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use montgomery_modint::{Mod998244353, MontgomeryModint};

    #[test]
    fn self_change_ntt_test() {
        type Modint = MontgomeryModint<Mod998244353>;
        let cache = FftCache::new();
        for i in 15..=20 {
            let mut data = (0..1 << i).map(|v| Modint::raw(v)).collect::<Vec<_>>();
            let expect = data.clone();
            data.ntt_with_cache(&cache);
            data.intt_with_cache(&cache);
            assert_eq!(data, expect);
        }
    }
}
