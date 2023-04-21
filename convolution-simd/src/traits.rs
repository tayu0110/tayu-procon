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
    fn dot(self, rhs: &Self) -> Self;
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
    fn dot(self, rhs: &Self) -> Self { dot::<M>(self, &rhs) }
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
    fn dot(self, rhs: &Self) -> Self { unsafe { transmute(transmute::<_, Vec<MontgomeryModint<M>>>(self).dot(transmute(rhs))) } }
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
