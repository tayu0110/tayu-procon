use super::MontgomeryModint;
use modint_common::*;
use numeric::{One, Zero};
use std::arch::x86_64::{
    __m256i, _mm256_i32gather_epi32, _mm256_loadu_si256, _mm256_set1_epi32, _mm256_setzero_si256, _mm256_storeu_si256, _mm256_unpackhi_epi32, _mm256_unpackhi_epi64, _mm256_unpacklo_epi32,
    _mm256_unpacklo_epi64,
};
use std::marker::PhantomData;
use std::ops::{Add, Mul, Sub};

type Modint<M> = MontgomeryModint<M>;

#[derive(Clone, Copy)]
pub struct MontgomeryModintx8<M: Modulo> {
    val: __m256i,
    _phantom: PhantomData<fn() -> M>,
}

type Modintx8<M> = MontgomeryModintx8<M>;

impl<M: Modulo> Modintx8<M> {
    #[inline]
    pub fn splat_raw(val: u32) -> Self {
        unsafe {
            Self {
                val: mmulx8::<M>(_mm256_set1_epi32(val as i32), M::R2X8),
                _phantom: PhantomData,
            }
        }
    }

    #[inline]
    pub fn splat(val: Modint<M>) -> Self { Self::from_rawval(unsafe { _mm256_set1_epi32(val.val as i32) }) }

    #[inline]
    pub fn from_rawval(val: __m256i) -> Self { Self { val, _phantom: PhantomData } }

    #[inline]
    pub fn val(&self) -> __m256i { unsafe { mrestorex8::<M>(mreducex8::<M>(self.val)) } }

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
    pub unsafe fn load(head: *const Modint<M>) -> Self { Self { val: _mm256_loadu_si256(head as _), _phantom: PhantomData } }

    #[inline]
    pub unsafe fn store(&self, head: *mut Modint<M>) { unsafe { _mm256_storeu_si256(head as _, self.val) } }

    #[inline]
    pub unsafe fn gather(head: *const Modint<M>, vindex: __m256i) -> Self { Self::from_rawval(unsafe { _mm256_i32gather_epi32(head as _, vindex, 4) }) }

    #[inline]
    pub unsafe fn unpacklo64(self, other: Self) -> Self { Self::from_rawval(_mm256_unpacklo_epi64(self.val, other.val)) }

    #[inline]
    pub unsafe fn unpackhi64(self, other: Self) -> Self { Self::from_rawval(_mm256_unpackhi_epi64(self.val, other.val)) }

    #[inline]
    pub unsafe fn unpacklo32(self, other: Self) -> Self { Self::from_rawval(_mm256_unpacklo_epi32(self.val, other.val)) }

    #[inline]
    pub unsafe fn unpackhi32(self, other: Self) -> Self { Self::from_rawval(_mm256_unpackhi_epi32(self.val, other.val)) }
}

impl<M: Modulo> One for Modintx8<M> {
    #[inline]
    fn one() -> Self { Self::one() }
}

impl<M: Modulo> Zero for Modintx8<M> {
    #[inline]
    fn zero() -> Self { Self::zero() }
}

impl<M: Modulo> Add for Modintx8<M> {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self::Output {
        Self {
            val: unsafe { maddx8::<M>(self.val, rhs.val) },
            _phantom: PhantomData,
        }
    }
}

impl<M: Modulo> Sub for Modintx8<M> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            val: unsafe { msubx8::<M>(self.val, rhs.val) },
            _phantom: PhantomData,
        }
    }
}

impl<M: Modulo> Mul for Modintx8<M> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            val: unsafe { mmulx8::<M>(self.val, rhs.val) },
            _phantom: PhantomData,
        }
    }
}

impl<M: Modulo> std::fmt::Debug for Modintx8<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut dest = [0u32; 8];
        unsafe {
            _mm256_storeu_si256(dest.as_mut_ptr() as *mut _, self.val);
            write!(f, "{:?}", dest)
        }
    }
}
