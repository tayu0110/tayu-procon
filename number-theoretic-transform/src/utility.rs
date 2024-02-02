#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use montgomery_modint::MontgomeryModintx8;
use montgomery_modint::{Modulo, MontgomeryModint};

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

/// # Safety
/// No constraint. For apply `#[target_feature(...)]`.
#[inline]
#[target_feature(enable = "avx", enable = "avx2")]
pub unsafe fn u32tomint<M: Modulo>(a: &mut [u32]) {
    let mut it = a.chunks_exact_mut(8);
    for v in it.by_ref() {
        Modintx8::<M>::convert_from_u32slice(v).store(v.as_mut_ptr() as _);
    }
    it.into_remainder()
        .iter_mut()
        .for_each(|a| *a = Modint::<M>::from(*a).rawval());
}

/// # Safety
/// No constraint. For apply `#[target_feature(...)]`.
#[inline]
#[target_feature(enable = "avx", enable = "avx2")]
pub unsafe fn minttou32<M: Modulo>(a: &mut [Modint<M>]) {
    let mut it = a.chunks_exact_mut(8);
    for v in it.by_ref() {
        Modintx8::from_rawval(Modintx8::load(v.as_ptr()).val()).store(v.as_mut_ptr());
    }
    it.into_remainder()
        .iter_mut()
        .for_each(|a| *a = Modint::from_rawval(a.val()));
}
