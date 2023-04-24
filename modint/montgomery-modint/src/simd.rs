use super::MontgomeryModint;
use modint_common::Modulo;
use numeric::{One, Zero};
use std::arch::x86_64::{
    __m256i, _mm256_add_epi32, _mm256_and_si256, _mm256_blend_epi32, _mm256_cmpeq_epi32, _mm256_i32gather_epi32, _mm256_loadu_si256, _mm256_max_epu32, _mm256_min_epu32, _mm256_mul_epu32,
    _mm256_mullo_epi32, _mm256_set1_epi32, _mm256_setzero_si256, _mm256_shuffle_epi32, _mm256_storeu_si256, _mm256_sub_epi32, _mm256_xor_si256,
};
use std::marker::PhantomData;
use std::ops::{Add, Mul, Sub};

#[derive(Clone, Copy)]
pub struct MontgomeryModintx8<M: Modulo> {
    val: __m256i,
    _phantom: PhantomData<fn() -> M>,
}

impl<M: Modulo> MontgomeryModintx8<M> {
    #[inline]
    #[target_feature(enable = "avx")]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_reduction(t: __m256i) -> __m256i {
        // t <- MR(T) = floor(T/R) - floor((TN' mod R)*N/R)
        //  if t < 0 then return t + N else return t
        //      T := a (0 <= T < NR)
        //      N := MOD
        //      N':= MOD_INV    NN' = 1 (mod R)
        //      R := R
        let t_ndash = _mm256_mullo_epi32(t, M::MOD_INVX8);
        let t_ndash_n_lo = _mm256_mul_epu32(t_ndash, M::MODX8);
        let t_ndash_n_hi = _mm256_mul_epu32(_mm256_shuffle_epi32(t_ndash, 0b10_11_00_01), M::MODX8);
        let mr = _mm256_blend_epi32(_mm256_shuffle_epi32(t_ndash_n_lo, 0b10_11_00_01), t_ndash_n_hi, 0b10101010);
        let zero = _mm256_setzero_si256();
        let mask = _mm256_cmpeq_epi32(mr, zero);
        let mask = _mm256_and_si256(M::MODX8, _mm256_xor_si256(mask, _mm256_cmpeq_epi32(mask, mask)));
        _mm256_sub_epi32(mask, mr)
    }

    #[inline]
    #[target_feature(enable = "avx2")]
    // Parallelization of Montgomery Multiplication
    unsafe fn montgomery_multiplication(ws: __m256i, cs: __m256i) -> __m256i {
        let t1 = _mm256_mul_epu32(ws, cs);
        let t2 = _mm256_mul_epu32(_mm256_shuffle_epi32(ws, 0b10_11_00_01), _mm256_shuffle_epi32(cs, 0b10_11_00_01));
        let t_modinv = _mm256_mullo_epi32(_mm256_blend_epi32(t1, _mm256_shuffle_epi32(t2, 0b10_11_00_01), 0b10101010), M::MOD_INVX8);
        let c = _mm256_blend_epi32(
            _mm256_shuffle_epi32(_mm256_mul_epu32(t_modinv, M::MODX8), 0b10_11_00_01),
            _mm256_mul_epu32(_mm256_shuffle_epi32(t_modinv, 0b10_11_00_01), M::MODX8),
            0b10101010,
        );
        let t = _mm256_blend_epi32(_mm256_shuffle_epi32(t1, 0b10_11_00_01), t2, 0b10101010);
        let one = _mm256_cmpeq_epi32(c, c);
        let mask = _mm256_and_si256(M::MODX8, _mm256_xor_si256(one, _mm256_cmpeq_epi32(_mm256_min_epu32(t, c), c)));
        _mm256_add_epi32(mask, _mm256_sub_epi32(t, c))
    }

    #[inline]
    pub fn splat(val: u32) -> Self { Self::splat_unchecked(val.rem_euclid(M::MOD)) }

    #[inline]
    pub fn splat_unchecked(val: u32) -> Self {
        unsafe {
            let val = Self::montgomery_multiplication(_mm256_set1_epi32(val as i32), M::R2X8);
            Self { val, _phantom: PhantomData }
        }
    }

    #[inline]
    pub fn splat_raw(val: MontgomeryModint<M>) -> Self { Self::from_rawval(unsafe { _mm256_set1_epi32(val.val as i32) }) }

    #[inline]
    pub fn from_rawval(val: __m256i) -> Self { Self { val, _phantom: PhantomData } }

    #[inline]
    pub fn val(&self) -> __m256i { unsafe { Self::montgomery_reduction(self.val) } }

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

    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn _mm256_add_mod_epi32(a: __m256i, b: __m256i) -> __m256i {
        let diff = _mm256_sub_epi32(M::MODX8, a);
        let mask = _mm256_cmpeq_epi32(diff, _mm256_max_epu32(diff, b));
        let val = _mm256_add_epi32(_mm256_sub_epi32(a, M::MODX8), b);
        _mm256_add_epi32(val, _mm256_and_si256(mask, M::MODX8))
    }

    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn _mm256_sub_mod_epi32(a: __m256i, b: __m256i) -> __m256i {
        let mask = _mm256_cmpeq_epi32(b, _mm256_max_epu32(a, b));
        let c_neg = _mm256_sub_epi32(a, b);
        _mm256_add_epi32(c_neg, _mm256_and_si256(M::MODX8, mask))
    }
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
    fn add(self, rhs: Self) -> Self::Output {
        let val = unsafe { Self::_mm256_add_mod_epi32(self.val, rhs.val) };
        Self { val, _phantom: PhantomData }
    }
}

impl<M: Modulo> Sub for MontgomeryModintx8<M> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        let val = unsafe { Self::_mm256_sub_mod_epi32(self.val, rhs.val) };
        Self { val, _phantom: PhantomData }
    }
}

impl<M: Modulo> Mul for MontgomeryModintx8<M> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            val: unsafe { Self::montgomery_multiplication(self.val, rhs.val) },
            _phantom: PhantomData,
        }
    }
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
