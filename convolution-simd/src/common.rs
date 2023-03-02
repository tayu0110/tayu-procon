#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{
    __m128i, __m256i, _mm256_add_epi32, _mm256_blend_epi32, _mm256_blendv_epi8, _mm256_cmpgt_epi32, _mm256_min_epu32, _mm256_mul_epu32, _mm256_mullo_epi32, _mm256_setzero_si256, _mm256_shuffle_epi32,
    _mm256_store_si256, _mm256_sub_epi32, _mm_add_epi32, _mm_blend_epi32, _mm_min_epu32, _mm_mul_epu32, _mm_mullo_epi32, _mm_shuffle_epi32, _mm_sub_epi32,
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
// ws: [w0, w1, w2, w3, w4, w5, w6, w7]
pub unsafe fn montgomery_reduction_u32x8(t: __m256i, modulo: __m256i, modulo_inv: __m256i) -> __m256i {
    // t <- MR(T) = floor(T/R) - floor((TN' mod R)*N/R)
    //  if t < 0 then return t + N else return t
    //      T := a (0 <= T < NR)
    //      N := MOD
    //      N':= MOD_INV    NN' = 1 (mod R)
    //      R := R
    // TN' = [w0modinvlo, w1modinvlo, w2modinvlo, w3modinvlo, w4modinvlo, w5modinvlo, w6modinvlo, w7modinvlo]
    let t_ndash = _mm256_mullo_epi32(t, modulo_inv);
    // (TN' mod R)*N (lo) = [w0modinvlo * mod, w2modinvlo * mod, w4modinvlo * mod, w6modinvlo * mod]
    let t_ndash_n_lo = _mm256_mul_epu32(t_ndash, modulo);
    // (TN' mod R)*N (hi) = [w1modinvlo * mod, w3modinvlo * mod, w5modinvlo * mod, w7modinvlo * mod]
    let t_ndash_n_hi = _mm256_mul_epu32(_mm256_shuffle_epi32(t_ndash, 0b10_11_00_01), modulo);
    let zero = _mm256_setzero_si256();
    let mr = _mm256_sub_epi32(zero, _mm256_blend_epi32(_mm256_shuffle_epi32(t_ndash_n_lo, 0b10_11_00_01), t_ndash_n_hi, 0b10101010));
    // if 0 > mr
    //      return mr + modulo
    // else
    //      return mr
    _mm256_blendv_epi8(mr, _mm256_add_epi32(mr, modulo), _mm256_cmpgt_epi32(zero, mr))
}

#[inline]
#[target_feature(enable = "avx2")]
// ws: [w0, w1, w2, w3, w4, w5, w6, w7]
// cs: [c0, c1, c2, c3, c4, c5, c6, c7]
//  -> [w0c0, w1c1, w2c2, w3c3, w4c4, w5c5, w6c6, w7c7]
pub unsafe fn montgomery_multiplication_u32x8(ws: __m256i, cs: __m256i, modulo: __m256i, modulo_inv: __m256i) -> __m256i {
    // Parallelization of Montgomery Multiplication
    // ws    = [w0, w1, w2, w3, w4, w5, w6, w7], cs = [c0, c1, c2, c3, c4, c5, c6, c7]
    // t1    = [w0c0lo, w0c0hi, w2c2lo, w2c2hi, w4c4lo, w4c4hi, w6c6lo, w6c6hi]
    let t1 = _mm256_mul_epu32(ws, cs);
    // t2    = [w1c1lo, w1c1hi, w3c3lo, w3c3hi, w5c5lo, w5c5hi, w7c7lo, w7c7hi]
    let t2 = _mm256_mul_epu32(_mm256_shuffle_epi32(ws, 0b10_11_00_01), _mm256_shuffle_epi32(cs, 0b10_11_00_01));
    // t_modinv = [(w0c0lo.wrap_mul(modinv), w1c1lo.wrap_mul(modinv)), (w2c2lo.wrap_mul(modinv), w3c3lo.wrap_mul(modinv)), (w4c4lo.wrap_mul(modinv), w5c5lo.wrap_mul(modinv)), (w6c6lo.wrap_mul(modinv), w7c7lo.wrap_mul(modinv))]
    let t_modinv = _mm256_mullo_epi32(_mm256_blend_epi32(t1, _mm256_shuffle_epi32(t2, 0b10_11_00_01), 0b10101010), modulo_inv);
    // c     = [c1[0], c2[0], c1[1], c2[1], c1[2], c2[2], c1[3], c2[3]]
    // MR(t) = t_hi - (wxcxlo.wrap_mul(modinv) as u64 * mod as u64 >> 32)
    //       = t_hi - u_hi
    //       = c_hi
    //      if c[i] >= mod then return c[i] - mod else return c[i]
    // Instead of 32-bit right shift, shuffle is used to swap the upper and lower 32 bits of a 64-bit integer.
    // At this point, the lower 32 bits are all zeros, so this is no problem.
    //      c1                                      = [0, MR(t1[0]), 0, MR(t1[1]), 0, MR(t1[2]), 0, MR(t1[3])]
    //      _mm256_shuffle_epi32(c1, 0b10_11_00_01) = [MR(t1[0]), 0,         MR(t1[1]), 0,         MR(t1[2]), 0,         MR(t1[3]), 0        ]
    //      c2                                      = [0,         MR(t2[0]), 0,         MR(t2[1]), 0,         MR(t2[2]), 0,         MR(t2[3])]
    //      _mm256_blend_epi32(_mm256_shuffle_epi32(c1, 0b10_11_00_01), c2, 0b10101010)
    //                                              = [MR(t1[0]), MR(t2[0]), MR(t1[1]), MR(t2[1]), MR(t1[2]), MR(t2[2]), MR(t1[3]), MR(t2[3])]
    let c_neg = _mm256_blend_epi32(
        _mm256_shuffle_epi32(_mm256_sub_epi32(t1, _mm256_mul_epu32(t_modinv, modulo)), 0b10_11_00_01),
        _mm256_sub_epi32(t2, _mm256_mul_epu32(_mm256_shuffle_epi32(t_modinv, 0b10_11_00_01), modulo)),
        0b10101010,
    );
    // if modulo > c
    //      return c
    // else
    //      return c_neg
    _mm256_min_epu32(_mm256_add_epi32(c_neg, modulo), c_neg)
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
    let c_neg = _mm_blend_epi32(
        _mm_shuffle_epi32(_mm_sub_epi32(t1, _mm_mul_epu32(t_modinv, modulo)), 0b10_11_00_01),
        _mm_sub_epi32(t2, _mm_mul_epu32(_mm_shuffle_epi32(t_modinv, 0b10_11_00_01), modulo)),
        0b1010,
    );
    _mm_min_epu32(_mm_add_epi32(c_neg, modulo), c_neg)
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn _mm256_add_mod_epi32(a: __m256i, b: __m256i, modulo: __m256i) -> __m256i {
    let c = _mm256_add_epi32(a, b);
    // if modulo > c
    //      return c
    // else
    //      return c_neg
    _mm256_min_epu32(c, _mm256_sub_epi32(c, modulo))
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn _mm256_sub_mod_epi32(a: __m256i, b: __m256i, modulo: __m256i) -> __m256i {
    let c_neg = _mm256_sub_epi32(a, b);
    let c = _mm256_add_epi32(c_neg, modulo);
    // if modulo > c
    //      return c
    // else
    //      return c_neg
    _mm256_min_epu32(c, c_neg)
}

#[inline]
#[target_feature(enable = "sse2")]
#[target_feature(enable = "sse4.1")]
pub unsafe fn _mm_add_mod_epi32(a: __m128i, b: __m128i, modulo: __m128i) -> __m128i {
    let c = _mm_add_epi32(a, b);
    _mm_min_epu32(c, _mm_sub_epi32(c, modulo))
}

#[inline]
#[target_feature(enable = "sse2")]
#[target_feature(enable = "sse4.1")]
pub unsafe fn _mm_sub_mod_epi32(a: __m128i, b: __m128i, modulo: __m128i) -> __m128i {
    let c_neg = _mm_sub_epi32(a, b);
    _mm_min_epu32(_mm_add_epi32(c_neg, modulo), c_neg)
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
