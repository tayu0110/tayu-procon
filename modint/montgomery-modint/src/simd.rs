use super::MontgomeryModint;
use modint_common::Modulo;
use numeric::{One, Zero};
use std::arch::x86_64::{__m256i, _mm256_i32gather_epi32, _mm256_loadu_si256, _mm256_set1_epi32, _mm256_setzero_si256, _mm256_storeu_si256};
use std::marker::PhantomData;
use std::ops::{Add, Mul, Sub};

#[derive(Clone, Copy)]
pub struct MontgomeryModintx8<M: Modulo> {
    val: __m256i,
    _phantom: PhantomData<fn() -> M>,
}

impl<M: Modulo> MontgomeryModintx8<M> {
    #[inline]
    pub fn splat(val: u32) -> Self { Self::splat_unchecked(val.rem_euclid(M::MOD)) }

    #[inline]
    pub fn splat_unchecked(val: u32) -> Self {
        unsafe {
            Self {
                val: M::multiplyx8(_mm256_set1_epi32(val as i32), M::R2X8),
                _phantom: PhantomData,
            }
        }
    }

    #[inline]
    pub fn splat_raw(val: MontgomeryModint<M>) -> Self { Self::from_rawval(unsafe { _mm256_set1_epi32(val.val as i32) }) }

    #[inline]
    pub fn from_rawval(val: __m256i) -> Self { Self { val, _phantom: PhantomData } }

    #[inline]
    pub fn val(&self) -> __m256i { M::restorex8(M::reducex8(self.val)) }

    #[inline]
    pub fn rawval(&self) -> __m256i { self.val }

    #[inline]
    pub fn one() -> Self { Self { val: M::RX8, _phantom: PhantomData } }

    #[inline]
    pub fn zero() -> Self {
        Self {
            val: unsafe { _mm256_setzero_si256() },
            _phantom: PhantomData,
        }
    }

    #[inline]
    pub fn load(slice: &[MontgomeryModint<M>]) -> Self {
        assert_eq!(slice.len(), 8);
        unsafe { Self::load_ptr(slice.as_ptr()) }
    }

    #[inline]
    pub unsafe fn load_ptr(head: *const MontgomeryModint<M>) -> Self { Self { val: _mm256_loadu_si256(head as _), _phantom: PhantomData } }

    #[inline]
    pub fn store(&self, slice: &mut [MontgomeryModint<M>]) {
        assert_eq!(slice.len(), 8);
        unsafe { self.store_ptr(slice.as_mut_ptr()) }
    }

    #[inline]
    pub unsafe fn store_ptr(&self, head: *mut MontgomeryModint<M>) { unsafe { _mm256_storeu_si256(head as _, self.val) } }

    #[inline]
    pub unsafe fn gather_ptr(head: *const MontgomeryModint<M>, vindex: __m256i) -> Self { Self::from_rawval(unsafe { _mm256_i32gather_epi32(head as _, vindex, 4) }) }
}

impl<M: Modulo> One for MontgomeryModintx8<M> {
    #[inline]
    fn one() -> Self { Self::one() }
}

impl<M: Modulo> Zero for MontgomeryModintx8<M> {
    #[inline]
    fn zero() -> Self { Self::zero() }
}

impl<M: Modulo> Add for MontgomeryModintx8<M> {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self::Output { Self { val: M::addx8(self.val, rhs.val), _phantom: PhantomData } }
}

impl<M: Modulo> Sub for MontgomeryModintx8<M> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self::Output { Self { val: M::subtractx8(self.val, rhs.val), _phantom: PhantomData } }
}

impl<M: Modulo> Mul for MontgomeryModintx8<M> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self::Output { Self { val: M::multiplyx8(self.val, rhs.val), _phantom: PhantomData } }
}

impl<M: Modulo> std::fmt::Debug for MontgomeryModintx8<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut dest = [0u32; 8];
        unsafe {
            _mm256_storeu_si256(dest.as_mut_ptr() as *mut _, self.val);
            write!(f, "{:?}", dest)
        }
    }
}
