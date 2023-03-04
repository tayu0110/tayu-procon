use std::arch::x86_64::_mm256_setzero_si256;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{
    __m128i, __m256i, _mm256_add_epi32, _mm256_and_si256, _mm256_blend_epi32, _mm256_cmpeq_epi32, _mm256_max_epu32, _mm256_mul_epu32, _mm256_mullo_epi32, _mm256_shuffle_epi32, _mm256_store_si256,
    _mm256_sub_epi32, _mm256_xor_si256, _mm_add_epi32, _mm_and_si128, _mm_blend_epi32, _mm_cmpeq_epi32, _mm_max_epu32, _mm_min_epu32, _mm_mul_epu32, _mm_mullo_epi32, _mm_shuffle_epi32, _mm_sub_epi32,
};

#[repr(C, align(32))]
pub struct AlignedArrayu32x8 {
    pub val: [u32; 8],
}

#[repr(C, align(32))]
pub struct AlignedArrayu64x4 {
    pub val: [u64; 4],
}

#[inline]
#[target_feature(enable = "avx")]
#[target_feature(enable = "avx2")]
pub unsafe fn montgomery_reduction_u32x8(t: __m256i, modulo: __m256i, modulo_inv: __m256i) -> __m256i {
    // t <- MR(T) = floor(T/R) - floor((TN' mod R)*N/R)
    //  if t < 0 then return t + N else return t
    //      T := a (0 <= T < NR)
    //      N := MOD
    //      N':= MOD_INV    NN' = 1 (mod R)
    //      R := R
    let t_ndash = _mm256_mullo_epi32(t, modulo_inv);
    let t_ndash_n_lo = _mm256_mul_epu32(t_ndash, modulo);
    let t_ndash_n_hi = _mm256_mul_epu32(_mm256_shuffle_epi32(t_ndash, 0b10_11_00_01), modulo);
    let mr = _mm256_blend_epi32(_mm256_shuffle_epi32(t_ndash_n_lo, 0b10_11_00_01), t_ndash_n_hi, 0b10101010);
    let zero = _mm256_setzero_si256();
    let mask = _mm256_cmpeq_epi32(mr, zero);
    let mask = _mm256_and_si256(modulo, _mm256_xor_si256(mask, _mm256_cmpeq_epi32(mask, mask)));
    _mm256_sub_epi32(mask, mr)
}

#[inline]
#[target_feature(enable = "avx2")]
// Parallelization of Montgomery Multiplication
pub unsafe fn montgomery_multiplication_u32x8(ws: __m256i, cs: __m256i, modulo: __m256i, modulo_inv: __m256i) -> __m256i {
    let t1 = _mm256_mul_epu32(ws, cs);
    let t2 = _mm256_mul_epu32(_mm256_shuffle_epi32(ws, 0b10_11_00_01), _mm256_shuffle_epi32(cs, 0b10_11_00_01));
    let t_modinv = _mm256_mullo_epi32(_mm256_blend_epi32(t1, _mm256_shuffle_epi32(t2, 0b10_11_00_01), 0b10101010), modulo_inv);
    let c = _mm256_blend_epi32(
        _mm256_shuffle_epi32(_mm256_mul_epu32(t_modinv, modulo), 0b10_11_00_01),
        _mm256_mul_epu32(_mm256_shuffle_epi32(t_modinv, 0b10_11_00_01), modulo),
        0b10101010,
    );
    let t = _mm256_blend_epi32(_mm256_shuffle_epi32(t1, 0b10_11_00_01), t2, 0b10101010);
    let mask = _mm256_and_si256(modulo, _mm256_cmpeq_epi32(_mm256_max_epu32(t, c), c));
    _mm256_add_epi32(mask, _mm256_sub_epi32(t, c))
}

#[inline]
#[target_feature(enable = "sse2")]
#[target_feature(enable = "sse4.1")]
pub unsafe fn montgomery_multiplication_u32x2_sse(ws: __m128i, cs: __m128i, modulo: __m128i, modulo_inv: __m128i) -> __m128i {
    let t = _mm_mul_epu32(ws, cs);
    let c_neg = _mm_sub_epi32(t, _mm_mul_epu32(_mm_mullo_epi32(t, modulo_inv), modulo));
    _mm_shuffle_epi32(_mm_min_epu32(_mm_add_epi32(c_neg, modulo), c_neg), 0b10_11_00_01)
}

#[inline]
#[target_feature(enable = "sse2")]
#[target_feature(enable = "sse4.1")]
#[target_feature(enable = "avx2")]
pub unsafe fn montgomery_multiplication_u32x4_sse(ws: __m128i, cs: __m128i, modulo: __m128i, modulo_inv: __m128i) -> __m128i {
    let t1 = _mm_mul_epu32(ws, cs);
    let t2 = _mm_mul_epu32(_mm_shuffle_epi32(ws, 0b10_11_00_01), _mm_shuffle_epi32(cs, 0b10_11_00_01));
    let t_modinv = _mm_mullo_epi32(_mm_blend_epi32(t1, _mm_shuffle_epi32(t2, 0b10_11_00_01), 0b1010), modulo_inv);
    let c = _mm_blend_epi32(
        _mm_shuffle_epi32(_mm_mul_epu32(t_modinv, modulo), 0b10_11_00_01),
        _mm_mul_epu32(_mm_shuffle_epi32(t_modinv, 0b10_11_00_01), modulo),
        0b1010,
    );
    let t = _mm_blend_epi32(_mm_shuffle_epi32(t1, 0b10_11_00_01), t2, 0b1010);
    let mask = _mm_and_si128(modulo, _mm_cmpeq_epi32(_mm_max_epu32(t, c), c));
    _mm_add_epi32(mask, _mm_sub_epi32(t, c))
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn _mm256_add_mod_epi32(a: __m256i, b: __m256i, modulo: __m256i) -> __m256i {
    let diff = _mm256_sub_epi32(modulo, a);
    let mask = _mm256_cmpeq_epi32(diff, _mm256_max_epu32(diff, b));
    let val = _mm256_add_epi32(_mm256_sub_epi32(a, modulo), b);
    _mm256_add_epi32(val, _mm256_and_si256(mask, modulo))
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn _mm256_sub_mod_epi32(a: __m256i, b: __m256i, modulo: __m256i) -> __m256i {
    let mask = _mm256_cmpeq_epi32(b, _mm256_max_epu32(a, b));
    let c_neg = _mm256_sub_epi32(a, b);
    _mm256_add_epi32(c_neg, _mm256_and_si256(modulo, mask))
}

#[inline]
#[target_feature(enable = "sse2")]
#[target_feature(enable = "sse4.1")]
pub unsafe fn _mm_add_mod_epi32(a: __m128i, b: __m128i, modulo: __m128i) -> __m128i {
    let diff = _mm_sub_epi32(modulo, a);
    let mask = _mm_cmpeq_epi32(diff, _mm_max_epu32(diff, b));
    let val = _mm_add_epi32(_mm_sub_epi32(a, modulo), b);
    _mm_add_epi32(val, _mm_and_si128(mask, modulo))
}

#[inline]
#[target_feature(enable = "sse2")]
#[target_feature(enable = "sse4.1")]
pub unsafe fn _mm_sub_mod_epi32(a: __m128i, b: __m128i, modulo: __m128i) -> __m128i {
    let mask = _mm_cmpeq_epi32(b, _mm_max_epu32(a, b));
    let c_neg = _mm_sub_epi32(a, b);
    _mm_add_epi32(c_neg, _mm_and_si128(modulo, mask))
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn _mm256_debug_print(a: __m256i, var_name: &str) {
    let mut dest = AlignedArrayu32x8 { val: [0u32; 8] };
    _mm256_store_si256(dest.val.as_mut_ptr() as *mut _, a);
    eprintln!("{}: {:?}", var_name, dest.val);
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn radix_4_innerx8(c0: __m256i, c1: __m256i, c2: __m256i, c3: __m256i, modulo: __m256i, modulo_inv: __m256i, prim_root: __m256i) -> (__m256i, __m256i, __m256i, __m256i) {
    let c1mc3im = montgomery_multiplication_u32x8(_mm256_sub_mod_epi32(c1, c3, modulo), prim_root, modulo, modulo_inv);
    let c1pc3 = _mm256_add_mod_epi32(c1, c3, modulo);
    let c0pc2 = _mm256_add_mod_epi32(c0, c2, modulo);
    let c0mc2 = _mm256_sub_mod_epi32(c0, c2, modulo);
    (
        _mm256_add_mod_epi32(c0pc2, c1pc3, modulo),
        _mm256_add_mod_epi32(c0mc2, c1mc3im, modulo),
        _mm256_sub_mod_epi32(c0pc2, c1pc3, modulo),
        _mm256_sub_mod_epi32(c0mc2, c1mc3im, modulo),
    )
}

#[inline]
#[target_feature(enable = "sse2")]
#[target_feature(enable = "sse4.1")]
pub unsafe fn radix_4_innerx2_sse(c0: __m128i, c1: __m128i, c2: __m128i, c3: __m128i, modulo: __m128i, modulo_inv: __m128i, prim_root: __m128i) -> (__m128i, __m128i, __m128i, __m128i) {
    let c1mc3im = montgomery_multiplication_u32x2_sse(_mm_sub_mod_epi32(c1, c3, modulo), prim_root, modulo, modulo_inv);
    let c1pc3 = _mm_add_mod_epi32(c1, c3, modulo);
    let c0pc2 = _mm_add_mod_epi32(c0, c2, modulo);
    let c0mc2 = _mm_sub_mod_epi32(c0, c2, modulo);
    (
        _mm_add_mod_epi32(c0pc2, c1pc3, modulo),
        _mm_add_mod_epi32(c0mc2, c1mc3im, modulo),
        _mm_sub_mod_epi32(c0pc2, c1pc3, modulo),
        _mm_sub_mod_epi32(c0mc2, c1mc3im, modulo),
    )
}

#[inline]
#[target_feature(enable = "sse2")]
#[target_feature(enable = "sse4.1")]
#[target_feature(enable = "avx2")]
pub unsafe fn radix_4_innerx4_sse(c0: __m128i, c1: __m128i, c2: __m128i, c3: __m128i, modulo: __m128i, modulo_inv: __m128i, prim_root: __m128i) -> (__m128i, __m128i, __m128i, __m128i) {
    let c1mc3im = montgomery_multiplication_u32x4_sse(_mm_sub_mod_epi32(c1, c3, modulo), prim_root, modulo, modulo_inv);
    let c1pc3 = _mm_add_mod_epi32(c1, c3, modulo);
    let c0pc2 = _mm_add_mod_epi32(c0, c2, modulo);
    let c0mc2 = _mm_sub_mod_epi32(c0, c2, modulo);
    (
        _mm_add_mod_epi32(c0pc2, c1pc3, modulo),
        _mm_add_mod_epi32(c0mc2, c1mc3im, modulo),
        _mm_sub_mod_epi32(c0pc2, c1pc3, modulo),
        _mm_sub_mod_epi32(c0mc2, c1mc3im, modulo),
    )
}
