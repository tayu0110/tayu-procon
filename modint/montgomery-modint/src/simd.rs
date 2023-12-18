#![allow(clippy::missing_safety_doc, clippy::inconsistent_digit_grouping)]
use super::MontgomeryModint;
use modint_common::*;
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use std::arch::x86_64::{
    __m256i, _mm256_i32gather_epi32, _mm256_loadu_si256, _mm256_permute2x128_si256,
    _mm256_set1_epi32, _mm256_setzero_si256, _mm256_shuffle_epi32, _mm256_storeu_si256,
    _mm256_unpackhi_epi32, _mm256_unpackhi_epi64, _mm256_unpacklo_epi32, _mm256_unpacklo_epi64,
};
use std::marker::PhantomData;
use std::ops::{Add, Mul, Sub};
use zero_one::{One, Zero};

type Modint<M> = MontgomeryModint<M>;

#[derive(Clone, Copy)]
pub struct MontgomeryModintx8<M: Modulo> {
    val: __m256i,
    _phantom: PhantomData<fn() -> M>,
}

type Modintx8<M> = MontgomeryModintx8<M>;

impl<M: Modulo> Modintx8<M> {
    /// `val` should **NOT** be Montgomery Representation.
    /// After `val` is loaded, this method converts `val` into Montgomery Representation.
    #[inline]
    pub fn splat_raw(val: u32) -> Self {
        unsafe {
            Self {
                val: mmulx8::<M>(_mm256_set1_epi32(val as i32), M::R2X8),
                _phantom: PhantomData,
            }
        }
    }

    /// `slice` should **NOT** be Montgomery Representation.
    /// After `slice` is loaded, this method converts the values of `slice` into Montgomery Representation.
    pub unsafe fn convert_from_u32slice(slice: &[u32]) -> Self {
        Self {
            val: (Self::load(slice.as_ptr() as _) * Self::from_rawval(M::R2X8)).rawval(),
            _phantom: PhantomData,
        }
    }

    #[inline]
    pub fn splat(val: Modint<M>) -> Self {
        Self::from_rawval(unsafe { _mm256_set1_epi32(val.val as i32) })
    }

    /// `val` should have be converted to Montgomery Representation.
    /// Internally, this method simply loads `val` does no other operations.
    #[inline]
    pub fn from_rawval(val: __m256i) -> Self {
        Self { val, _phantom: PhantomData }
    }

    #[inline]
    pub fn val(&self) -> __m256i {
        unsafe { mrestorex8::<M>(mreducex8::<M>(self.val)) }
    }

    #[inline]
    pub fn rawval(&self) -> __m256i {
        self.val
    }

    #[inline]
    pub fn one() -> Self {
        Self { val: M::RX8, _phantom: PhantomData }
    }

    #[inline]
    pub fn zero() -> Self {
        Self {
            val: unsafe { _mm256_setzero_si256() },
            _phantom: PhantomData,
        }
    }

    #[inline]
    #[target_feature(enable = "avx")]
    pub unsafe fn load(head: *const Modint<M>) -> Self {
        Self { val: _mm256_loadu_si256(head as _), _phantom: PhantomData }
    }

    #[inline]
    #[target_feature(enable = "avx")]
    pub unsafe fn store(&self, head: *mut Modint<M>) {
        unsafe { _mm256_storeu_si256(head as _, self.val) }
    }

    #[inline]
    #[target_feature(enable = "avx2")]
    pub unsafe fn gather(head: *const Modint<M>, vindex: __m256i) -> Self {
        Self::from_rawval(unsafe { _mm256_i32gather_epi32(head as _, vindex, 4) })
    }

    #[inline]
    #[target_feature(enable = "avx2")]
    pub unsafe fn unpacklo64(self, other: Self) -> Self {
        Self::from_rawval(_mm256_unpacklo_epi64(self.val, other.val))
    }

    #[inline]
    #[target_feature(enable = "avx2")]
    pub unsafe fn unpackhi64(self, other: Self) -> Self {
        Self::from_rawval(_mm256_unpackhi_epi64(self.val, other.val))
    }

    #[inline]
    #[target_feature(enable = "avx2")]
    pub unsafe fn unpacklo32(self, other: Self) -> Self {
        Self::from_rawval(_mm256_unpacklo_epi32(self.val, other.val))
    }

    #[inline]
    #[target_feature(enable = "avx2")]
    pub unsafe fn unpackhi32(self, other: Self) -> Self {
        Self::from_rawval(_mm256_unpackhi_epi32(self.val, other.val))
    }

    /// 0: self\[127:0\], 1: self\[255:128\], 2: other\[127:0\], 3: other\[255:128\]
    /// the upper of 4-bit of IMM8 is YMM of return value, and the lower of 4-bit of IMM8 is XMM of return value.
    ///
    /// # Example
    /// ```rust
    /// use std::mem::transmute;
    /// use std::arch::x86_64::__m256i;
    /// use montgomery_modint::{Mod998244353, MontgomeryModintx8};
    ///
    /// type Modintx8 = MontgomeryModintx8<Mod998244353>;
    ///
    /// let base: __m256i = unsafe { transmute([0u32, 1, 2, 3, 4, 5, 6, 7]) };
    /// let m = Modintx8::from_rawval(base);
    /// let other: __m256i = unsafe { transmute([10u32, 11, 12, 13, 14, 15, 16, 17]) };
    /// let n = Modintx8::from_rawval(other);
    /// let mut buf = [0u32; 8];
    ///
    /// unsafe {
    ///     // swap YMM and XMM on self
    ///     let res = m.permute2x128::<0x01>(m);
    ///     res.store(buf.as_mut_ptr() as _);
    ///     assert_eq!(buf, [4, 5, 6, 7, 0, 1, 2, 3]);
    ///
    ///     // copy XMM to YMM on self
    ///     let res = m.permute2x128::<0x00>(m);
    ///     res.store(buf.as_mut_ptr() as _);
    ///     assert_eq!(buf, [0, 1, 2, 3, 0, 1, 2, 3]);
    ///
    ///     // merge YMM on other and XMM on self
    ///     let res = m.permute2x128::<0x30>(n);
    ///     res.store(buf.as_mut_ptr() as _);
    ///     assert_eq!(buf, [0, 1, 2, 3, 14, 15, 16, 17]);
    ///
    ///     // merge XMM on other and YMM on self
    ///     let res = m.permute2x128::<0x21>(n);
    ///     res.store(buf.as_mut_ptr() as _);
    ///     assert_eq!(buf, [4, 5, 6, 7, 10, 11, 12, 13]);
    /// }
    /// ```
    #[inline]
    #[target_feature(enable = "avx2")]
    pub unsafe fn permute2x128<const IMM8: i32>(self, other: Self) -> Self {
        Self::from_rawval(_mm256_permute2x128_si256::<IMM8>(self.val, other.val))
    }

    #[inline]
    pub fn accumulate(self) -> Modint<M> {
        let mut buf = [Modint::zero(); 8];
        unsafe {
            let add01 = self + Self::from_rawval(_mm256_shuffle_epi32::<0b10_11_00_01>(self.val));
            let add0123 =
                add01 + Self::from_rawval(_mm256_shuffle_epi32::<0b01_00_11_10>(add01.val));
            add0123.store(buf.as_mut_ptr());
        }
        buf[0] + buf[4]
    }
}

impl<M: Modulo> One for Modintx8<M> {
    #[inline]
    fn one() -> Self {
        Self::one()
    }
}

impl<M: Modulo> Zero for Modintx8<M> {
    #[inline]
    fn zero() -> Self {
        Self::zero()
    }
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

#[cfg(test)]
mod tests {
    use super::*;

    type Modintx8 = MontgomeryModintx8<Mod998244353>;

    #[test]
    fn accumulate_test() {
        let buf = [
            1.into(),
            10.into(),
            100.into(),
            1000.into(),
            10000.into(),
            10000_0.into(),
            10000_00.into(),
            10000_000.into(),
        ];
        let reg = unsafe { Modintx8::load(buf.as_ptr()) };
        let acc = reg.accumulate();

        assert_eq!(acc.val(), 11111111);
    }
}
