use crate::cooley_tukey::cooley_tukey_radix_4_butterfly;
use crate::gentleman_sande::gentleman_sande_radix_4_butterfly_inv;

use super::fft_cache::FftCache;
use super::{dot, intt, ntt};
use montgomery_modint::{Modulo, MontgomeryModint, MontgomeryModintx8};
use std::arch::x86_64::_mm256_storeu_si256;
use std::mem::transmute;

pub trait Nttable<M: Modulo> {
    fn ntt(self) -> Self;
    fn intt(self) -> Self;
    fn ntt_with_cache(self, cache: &FftCache<M>) -> Self;
    fn intt_with_cache(self, cache: &FftCache<M>) -> Self;
    fn ntt_self(&mut self);
    fn intt_self(&mut self);
    fn ntt_self_with_cache(&mut self, cache: &FftCache<M>);
    fn intt_self_with_cache(&mut self, cache: &FftCache<M>);
    fn dot(self, rhs: &Self) -> Self;
    fn dot_assign(&mut self, rhs: &Self);
}

impl<M: Modulo> Nttable<M> for Vec<MontgomeryModint<M>> {
    fn ntt(self) -> Self {
        let len = self.len();
        assert_eq!(1 << len.trailing_zeros(), len);
        let cache = FftCache::new();
        self.ntt_with_cache(&cache)
    }
    fn intt(self) -> Self {
        let len = self.len();
        assert_eq!(1 << len.trailing_zeros(), len);
        let cache = FftCache::new();
        self.intt_with_cache(&cache)
    }
    fn ntt_with_cache(self, cache: &FftCache<M>) -> Self { ntt(self, &cache) }
    fn intt_with_cache(self, cache: &FftCache<M>) -> Self { intt(self, &cache) }
    fn ntt_self(&mut self) {
        let cache = FftCache::new();
        self.ntt_self_with_cache(&cache);
    }
    fn intt_self(&mut self) {
        let cache = FftCache::new();
        self.intt_self_with_cache(&cache);
    }
    fn ntt_self_with_cache(&mut self, cache: &FftCache<M>) { unsafe { cooley_tukey_radix_4_butterfly(self.len(), self.len().trailing_zeros() as usize, self, cache) } }
    fn intt_self_with_cache(&mut self, cache: &FftCache<M>) {
        let n = self.len();
        unsafe {
            gentleman_sande_radix_4_butterfly_inv(n, n.trailing_zeros() as usize, self, cache);
            let ninv = MontgomeryModint::raw(n as u32).inv();
            if n < 8 {
                self.iter_mut().for_each(|a| *a *= ninv);
            } else {
                let ninv = MontgomeryModintx8::<M>::splat_raw(ninv);
                self.chunks_exact_mut(8).for_each(|v| (MontgomeryModintx8::load_ptr(v.as_ptr()) * ninv).store_ptr(v.as_mut_ptr()));
            }
        };
    }
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
    fn ntt(self) -> Self {
        let len = self.len();
        assert_eq!(1 << len.trailing_zeros(), len);
        let cache = FftCache::<M>::new();
        self.ntt_with_cache(&cache)
    }
    fn intt(self) -> Self {
        let len = self.len();
        assert_eq!(1 << len.trailing_zeros(), len);
        let cache = FftCache::<M>::new();
        self.intt_with_cache(&cache)
    }
    fn ntt_with_cache(self, cache: &FftCache<M>) -> Self { unsafe { transmute(convert_u32_to_modint(self).ntt_with_cache(cache)) } }
    fn intt_with_cache(self, cache: &FftCache<M>) -> Self { convert_modint_to_u32(unsafe { transmute::<_, Vec<MontgomeryModint<M>>>(self).intt_with_cache(cache) }) }
    fn ntt_self(&mut self) {
        let cache = FftCache::<M>::new();
        self.ntt_self_with_cache(&cache);
    }
    fn intt_self(&mut self) {
        let cache = FftCache::<M>::new();
        self.intt_self_with_cache(&cache);
    }
    fn ntt_self_with_cache(&mut self, cache: &FftCache<M>) {
        self.into_iter().for_each(|a| *a = MontgomeryModint::<M>::raw(*a).val);
        let a = unsafe { transmute::<_, &mut Vec<MontgomeryModint<M>>>(self) };
        a.ntt_self_with_cache(cache)
    }
    fn intt_self_with_cache(&mut self, cache: &FftCache<M>) {
        let a = unsafe { transmute::<_, &mut Vec<MontgomeryModint<M>>>(self) };
        a.intt_self_with_cache(cache);
        a.into_iter().for_each(|a| *a = MontgomeryModint::from_mont_expr(a.val()));
    }
    fn dot(self, rhs: &Self) -> Self { unsafe { transmute(transmute::<_, Vec<MontgomeryModint<M>>>(self).dot(transmute(rhs))) } }
    fn dot_assign(&mut self, rhs: &Self) {
        let a = unsafe { transmute::<_, &mut Vec<MontgomeryModint<M>>>(self) };
        let b = unsafe { transmute::<_, &Vec<MontgomeryModint<M>>>(rhs) };
        a.dot_assign(b);
    }
}

#[inline]
fn convert_u32_to_modint<M: Modulo>(mut a: Vec<u32>) -> Vec<MontgomeryModint<M>> {
    if a.len() < 8 {
        a.into_iter().map(|a| MontgomeryModint::from(a)).collect()
    } else {
        unsafe {
            a.chunks_exact_mut(8)
                .for_each(|v| (MontgomeryModintx8::<M>::load_ptr(v.as_ptr() as _) * MontgomeryModintx8::from_rawval(M::R2X8)).store_ptr(v.as_mut_ptr() as _));
            transmute(a)
        }
    }
}

#[inline]
fn convert_modint_to_u32<M: Modulo>(mut a: Vec<MontgomeryModint<M>>) -> Vec<u32> {
    if a.len() < 8 {
        a.into_iter().map(|a| a.val()).collect()
    } else {
        unsafe {
            a.chunks_exact_mut(8)
                .for_each(|v| _mm256_storeu_si256(v.as_mut_ptr() as _, MontgomeryModintx8::load_ptr(v.as_ptr()).val()));
            transmute(a)
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
            data.ntt_self_with_cache(&cache);
            data.intt_self_with_cache(&cache);
            assert_eq!(data, expect);
        }
    }
}
