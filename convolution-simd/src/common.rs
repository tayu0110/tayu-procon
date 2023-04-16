use montgomery_modint::Modulo;
#[cfg(target_arch = "x86")]
use std::arch::x86::*;
use std::arch::x86_64::_mm256_min_epu32;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{
    __m256i, _mm256_add_epi32, _mm256_and_si256, _mm256_blend_epi32, _mm256_cmpeq_epi32, _mm256_max_epu32, _mm256_mul_epu32, _mm256_mullo_epi32, _mm256_setzero_si256, _mm256_shuffle_epi32,
    _mm256_store_si256, _mm256_sub_epi32, _mm256_xor_si256,
};

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
// pub unsafe fn montgomery_reduction_u32x8(t: __m256i, modulo: __m256i, modulo_inv: __m256i) -> __m256i {
pub unsafe fn montgomery_reduction_u32x8<M: Modulo>(t: __m256i) -> __m256i {
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
pub unsafe fn montgomery_multiplication_u32x8<M: Modulo>(ws: __m256i, cs: __m256i) -> __m256i {
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
#[target_feature(enable = "avx2")]
pub unsafe fn _mm256_add_mod_epi32<M: Modulo>(a: __m256i, b: __m256i) -> __m256i {
    let diff = _mm256_sub_epi32(M::MODX8, a);
    let mask = _mm256_cmpeq_epi32(diff, _mm256_max_epu32(diff, b));
    let val = _mm256_add_epi32(_mm256_sub_epi32(a, M::MODX8), b);
    _mm256_add_epi32(val, _mm256_and_si256(mask, M::MODX8))
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn _mm256_sub_mod_epi32<M: Modulo>(a: __m256i, b: __m256i) -> __m256i {
    let mask = _mm256_cmpeq_epi32(b, _mm256_max_epu32(a, b));
    let c_neg = _mm256_sub_epi32(a, b);
    _mm256_add_epi32(c_neg, _mm256_and_si256(M::MODX8, mask))
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn _mm256_debug_print(a: __m256i, var_name: &str) {
    #[repr(C, align(32))]
    struct AlignedArrayu32x8 {
        pub val: [u32; 8],
    }
    let mut dest = AlignedArrayu32x8 { val: [0u32; 8] };
    _mm256_store_si256(dest.val.as_mut_ptr() as *mut _, a);
    eprintln!("{}: {:?}", var_name, dest.val);
}
