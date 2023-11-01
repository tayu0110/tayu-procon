#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use montgomery_modint::MontgomeryModintx8;
use montgomery_modint::{Modulo, MontgomeryModint};
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use std::arch::x86_64::_mm256_storeu_si256;

type Modint<M> = MontgomeryModint<M>;
#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
type Modintx8<M> = MontgomeryModintx8<M>;

#[inline]
// reference: https://www.kurims.kyoto-u.ac.jp/~ooura/fftman/ftmn1_25.html#sec1_2_5
pub fn bit_reverse<T>(deg: usize, a: &mut [T]) {
    let nh = deg >> 1;
    let nh1 = nh + 1;
    let mut i = 0;
    for j in (0..nh).step_by(2) {
        if j < i {
            a.swap(i, j);
            a.swap(i + nh1, j + nh1);
        }
        a.swap(j + nh, i + 1);
        let mut k = nh >> 1;
        i ^= k;
        while k > i {
            k >>= 1;
            i ^= k;
        }
    }
}

#[inline]
#[target_feature(enable = "avx")]
#[target_feature(enable = "avx2")]
pub(crate) unsafe fn u32tomint<M: Modulo>(a: &mut [u32]) {
    debug_assert_eq!(a.len(), 1 << a.len().trailing_zeros());

    if a.len() >= 8 {
        unsafe {
            let r2x8 = Modintx8::from_rawval(M::R2X8);
            for v in a.chunks_exact_mut(8) {
                let res = Modintx8::<M>::load(v.as_ptr() as _) * r2x8;
                res.store(v.as_mut_ptr() as _);
            }
        }
    } else {
        a.iter_mut().for_each(|a| *a = Modint::<M>::from(*a).val);
    }
}

#[inline]
#[target_feature(enable = "avx")]
#[target_feature(enable = "avx2")]
pub(crate) unsafe fn minttou32<M: Modulo>(a: &mut [Modint<M>]) {
    debug_assert_eq!(a.len(), 1 << a.len().trailing_zeros());

    if a.len() >= 8 {
        unsafe {
            for v in a.chunks_exact_mut(8) {
                let res = Modintx8::<M>::load(v.as_ptr());
                _mm256_storeu_si256(v.as_mut_ptr() as _, res.val())
            }
        }
    } else {
        a.iter_mut().for_each(|a| *a = Modint::from_rawval(a.val()));
    }
}
