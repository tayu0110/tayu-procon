use std::arch::x86_64::_mm256_setzero_si256;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{
    __m256i, _mm256_add_epi32, _mm256_blend_epi32, _mm256_blendv_epi8, _mm256_cmpgt_epi32, _mm256_mul_epu32, _mm256_mullo_epi32, _mm256_shuffle_epi32, _mm256_store_si256, _mm256_sub_epi32,
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
    _mm256_blendv_epi8(mr, _mm256_add_epi32(mr, modulo), _mm256_cmpgt_epi32(zero, mr))
}

#[inline]
#[target_feature(enable = "avx2")]
// ws: [(w0, 0), (w1, 0), (w2, 0), (w3, 0)]
// cs: [(c0, 0), (c1, 0), (c2, 0), (c3, 0)]
//  -> [w0c0, 0, w1c1, 0, w2c2, 0, w3c3, 0]
pub unsafe fn montgomery_multiplication_u32x4(ws: __m256i, cs: __m256i, modulo: __m256i, modulo_inv: __m256i) -> __m256i {
    // Parallelization of Montgomery Multiplication
    // ws    = [(w0, 0), (w1, 0), (w2, 0), (w3, 0)], cs = [(c0, 0), (c1, 0), (c2, 0), (c3, 0)]
    // t     = [(w0 * c0 as i64), (w1 * c1 as i64), (w2 * c2 as i64), (w3 * c3 as i64)]
    //       = [(w0c0lo, w0c0hi), (w1c1lo, w1c1hi), (w2c2lo, w2c2hi), (w3c3lo, w3c3hi)]
    let t = _mm256_mul_epu32(ws, cs);
    // tmi   = [(w0c0lo.wrap_mul(modinv), w0c0hi.wrap_mul(modinv)), (w1c1lo.wrap_mul(modinv), w1c1hi.wrap_mul(modinv)),
    //          (w2c2lo.wrap_mul(modinv), w2c2hi.wrap_mul(modinv)), (w3c3lo.wrap_mul(modinv), w3c3hi.wrap_mul(modinv))]
    let tmi = _mm256_mullo_epi32(t, modulo_inv);
    // u     = [(w0c0lo.wrap_mul(modinv) * mod as i64), (w1c1lo.wrap_mul(modinv) * mod as i64),
    //          (w2c2lo.wrap_mul(modinv) * mod as i64), (w3c3lo.wrap_mul(modinv) * mod as i64)]
    let u = _mm256_mul_epu32(tmi, modulo);
    // c_neg = [t0lo - u0lo, t0hi - u0hi, t1lo - u1lo,
    //          t2lo - u2lo, t2hi - u2hi, t3lo - u3lo]
    // MR(t) = wxcxhi - (wxcxlo.wrap_mul(modinv) as u64 * mod as u64 >> 32)
    //       = t_hi - u_hi
    //       = c_hi
    //      if c[i] < 0 then return c[i] + mod else return c[i]
    let c_neg = _mm256_sub_epi32(t, u);
    let c = _mm256_add_epi32(c_neg, modulo);
    // if modulo > c
    //      return c
    // else
    //      return c_neg
    let res = _mm256_blendv_epi8(c_neg, c, _mm256_cmpgt_epi32(modulo, c));
    // let res = _mm256_blendv_epi8(_mm256_sub_epi32(c, modulo), c, _mm256_cmpgt_epi32(modulo, c));
    // Instead of 32-bit right shift, shuffle is used to swap the upper and lower 32 bits of a 64-bit integer.
    // At this point, the lower 32 bits are all zeros, so this is no problem.
    _mm256_shuffle_epi32(res, 0b10_11_00_01)
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
    // t1mod = [(w0c0lo.wrap_mul(modinv), w0c0hi.wrap_mul(modinv)), (w2c2lo.wrap_mul(modinv), w2c2hi.wrap_mul(modinv)), (w4c4lo.wrap_mul(modinv), w4c4hi.wrap_mul(modinv)), (w6c6lo.wrap_mul(modinv), w6c6hi.wrap_mul(modinv))]
    let t1mod = _mm256_mullo_epi32(t1, modulo_inv);
    // t2mod = [(w1c1lo.wrap_mul(modinv), w1c1hi.wrap_mul(modinv)), (w3c3lo.wrap_mul(modinv), w3c3hi.wrap_mul(modinv)), (w5c5lo.wrap_mul(modinv), w5c5hi.wrap_mul(modinv)), (w7c7lo.wrap_mul(modinv), w7c7hi.wrap_mul(modinv))]
    let t2mod = _mm256_mullo_epi32(t2, modulo_inv);
    // u1    = [(w0c0lo.wrap_mul(modinv) * mod as i64), (w2c2lo.wrap_mul(modinv) * mod as i64), (w4c4lo.wrap_mul(modinv) * mod as i64), (w6c6lo.wrap_mul(modinv) * mod as i64)]
    let u1 = _mm256_mul_epu32(t1mod, modulo);
    // u2    = [(w1c1lo.wrap_mul(modinv) * mod as i64), (w3c3lo.wrap_mul(modinv) * mod as i64), (w5c5lo.wrap_mul(modinv) * mod as i64), (w7c7lo.wrap_mul(modinv) * mod as i64)]
    let u2 = _mm256_mul_epu32(t2mod, modulo);
    // c1    = [t + (w0c0lo.wrap_mul(modinv) * mod as i64), t + (w2c2lo.wrap_mul(modinv) * mod as i64), t + (w4c4lo.wrap_mul(modinv) * mod as i64), t + (w6c6lo.wrap_mul(modinv) * mod as i64)]
    let c1_neg = _mm256_sub_epi32(t1, u1);
    // c2    = [t + (w1c1lo.wrap_mul(modinv) * mod as i64), t + (w3c3lo.wrap_mul(modinv) * mod as i64), t + (w5c5lo.wrap_mul(modinv) * mod as i64), t + (w7c7lo.wrap_mul(modinv) * mod as i64)]
    let c2_neg = _mm256_sub_epi32(t2, u2);
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
    // let c = _mm256_blend_epi32(_mm256_shuffle_epi32(c1, 0b10_11_00_01), c2, 0b10101010);
    let c_neg = _mm256_blend_epi32(_mm256_shuffle_epi32(c1_neg, 0b10_11_00_01), c2_neg, 0b10101010);
    let c = _mm256_add_epi32(c_neg, modulo);
    // if modulo > c
    //      return c
    // else
    //      return c_neg
    _mm256_blendv_epi8(_mm256_sub_epi32(c, modulo), c, _mm256_cmpgt_epi32(modulo, c))
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn _mm256_add_mod_epi32(a: __m256i, b: __m256i, modulo: __m256i) -> __m256i {
    let c = _mm256_add_epi32(a, b);
    // if modulo > c
    //      return c
    // else
    //      return c_neg
    _mm256_blendv_epi8(_mm256_sub_epi32(c, modulo), c, _mm256_cmpgt_epi32(modulo, c))
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
    _mm256_blendv_epi8(c_neg, c, _mm256_cmpgt_epi32(modulo, c))
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
pub unsafe fn radix_4_innerx4(c0: __m256i, c1: __m256i, c2: __m256i, c3: __m256i, modulo: __m256i, modulo_inv: __m256i, prim_root: __m256i) -> (__m256i, __m256i, __m256i, __m256i) {
    let c0pc2 = _mm256_add_mod_epi32(c0, c2, modulo);
    let c0mc2 = _mm256_sub_mod_epi32(c0, c2, modulo);
    let c1pc3 = _mm256_add_mod_epi32(c1, c3, modulo);
    let c1mc3 = _mm256_sub_mod_epi32(c1, c3, modulo);
    let c1mc3im = montgomery_multiplication_u32x4(c1mc3, prim_root, modulo, modulo_inv);
    (
        _mm256_add_mod_epi32(c0pc2, c1pc3, modulo),
        _mm256_add_mod_epi32(c0mc2, c1mc3im, modulo),
        _mm256_sub_mod_epi32(c0pc2, c1pc3, modulo),
        _mm256_sub_mod_epi32(c0mc2, c1mc3im, modulo),
    )
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn radix_4_innerx8(c0: __m256i, c1: __m256i, c2: __m256i, c3: __m256i, modulo: __m256i, modulo_inv: __m256i, prim_root: __m256i) -> (__m256i, __m256i, __m256i, __m256i) {
    let c0pc2 = _mm256_add_mod_epi32(c0, c2, modulo);
    let c0mc2 = _mm256_sub_mod_epi32(c0, c2, modulo);
    let c1pc3 = _mm256_add_mod_epi32(c1, c3, modulo);
    let c1mc3 = _mm256_sub_mod_epi32(c1, c3, modulo);
    let c1mc3im = montgomery_multiplication_u32x8(c1mc3, prim_root, modulo, modulo_inv);
    (
        _mm256_add_mod_epi32(c0pc2, c1pc3, modulo),
        _mm256_add_mod_epi32(c0mc2, c1mc3im, modulo),
        _mm256_sub_mod_epi32(c0pc2, c1pc3, modulo),
        _mm256_sub_mod_epi32(c0mc2, c1mc3im, modulo),
    )
}
