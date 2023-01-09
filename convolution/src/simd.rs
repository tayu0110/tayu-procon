use super::FftCache;
use modint::{Mod998244353, Modulo, MontgomeryModint};
#[cfg(target_arch = "x86")]
use std::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{
    __m256i, _mm256_add_epi32, _mm256_blend_epi32, _mm256_blendv_epi8, _mm256_castsi128_si256, _mm256_castsi256_si128, _mm256_cmpgt_epi32, _mm256_extracti128_si256,
    _mm256_load_si256, _mm256_loadu_si256, _mm256_mul_epu32, _mm256_mullo_epi32, _mm256_set1_epi32, _mm256_set_epi32, _mm256_set_m128i, _mm256_shuffle_epi32,
    _mm256_store_si256, _mm256_storeu_si256, _mm256_sub_epi32, _mm256_unpackhi_epi32, _mm256_unpacklo_epi32, _mm256_unpacklo_epi64, _mm_load_si128, _mm_loadu_si128,
};

type Mint = MontgomeryModint<Mod998244353>;

#[repr(C, align(32))]
struct AlignedArrayu32x8 {
    val: [u32; 8],
}

#[repr(C, align(32))]
struct AlignedArrayu64x4 {
    val: [u64; 4],
}

#[inline]
#[target_feature(enable = "avx2")]
// ws: [(w0, 0), (w1, 0), (w2, 0), (w3, 0)]
// cs: [(c0, 0), (c1, 0), (c2, 0), (c3, 0)]
//  -> [w0c0, 0, w1c1, 0, w2c2, 0, w3c3, 0]
unsafe fn montgomery_multiplication_u32x4(ws: __m256i, cs: __m256i, modulo: __m256i, modulo_inv: __m256i) -> __m256i {
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
unsafe fn montgomery_multiplication_u32x8(ws: __m256i, cs: __m256i, modulo: __m256i, modulo_inv: __m256i) -> __m256i {
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
unsafe fn _mm256_add_mod_epi32(a: __m256i, b: __m256i, modulo: __m256i) -> __m256i {
    let c = _mm256_add_epi32(a, b);
    // if modulo > c
    //      return c
    // else
    //      return c_neg
    _mm256_blendv_epi8(_mm256_sub_epi32(c, modulo), c, _mm256_cmpgt_epi32(modulo, c))
}

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn _mm256_sub_mod_epi32(a: __m256i, b: __m256i, modulo: __m256i) -> __m256i {
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
unsafe fn _mm256_debug_print(a: __m256i, var_name: &str) {
    let mut dest = AlignedArrayu32x8 { val: [0u32; 8] };
    _mm256_store_si256(dest.val.as_mut_ptr() as *mut _, a);
    eprintln!("{}: {:?}", var_name, dest.val);
}

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn radix_4_innerx4(
    c0: __m256i,
    c1: __m256i,
    c2: __m256i,
    c3: __m256i,
    modulo: __m256i,
    modulo_inv: __m256i,
    prim_root: __m256i,
) -> (__m256i, __m256i, __m256i, __m256i) {
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
unsafe fn radix_4_innerx8(
    c0: __m256i,
    c1: __m256i,
    c2: __m256i,
    c3: __m256i,
    modulo: __m256i,
    modulo_inv: __m256i,
    prim_root: __m256i,
) -> (__m256i, __m256i, __m256i, __m256i) {
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

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn radix_2_kernel_gentleman_sande_avx2(width: usize, a: &mut [Mint]) {
    // offset = width >> 1;
    assert_eq!(width >> 1, 1);
    for a in a.chunks_exact_mut(2) {
        let c1 = a[1];
        a[1] = a[0] - c1;
        a[0] += c1;
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn radix_4_kernel_gentleman_sande_avx2(deg: usize, width: usize, a: &mut [Mint], twiddle: &[Mint]) {
    let log = width.trailing_zeros();
    let exp = deg >> log;

    // Constants for Montgomery Operation
    let modulo_inv = _mm256_set1_epi32(Mod998244353::MOD_INV as i32);
    let modulo = _mm256_set1_epi32(Mod998244353::MOD as i32);
    let prim_root = _mm256_set1_epi32(twiddle[deg >> 2].val as i32);

    let offset = width >> 2;
    if offset == 1 {
        let prim_root = twiddle[(twiddle.len() - 1) >> 2];
        for a in a.chunks_exact_mut(4) {
            let (c0, c1, c2, c3) = (a[0], a[1], a[2], a[3]);
            let (c0, c1, c2, c3) = {
                let c0pc2 = c0 + c2;
                let c0mc2 = c0 - c2;
                let c1pc3 = c1 + c3;
                let c1mc3 = c1 - c3;
                let c1mc3im = c1mc3 * prim_root;
                (c0pc2 + c1pc3, c0mc2 + c1mc3im, c0pc2 - c1pc3, c0mc2 - c1mc3im)
            };
            a[0] = c0;
            a[2] = c1;
            a[1] = c2;
            a[3] = c3;
        }
    } else if offset == 2 {
        let mut c0 = AlignedArrayu64x4 { val: [0; 4] };
        let mut c1 = AlignedArrayu64x4 { val: [0; 4] };
        let mut c2 = AlignedArrayu64x4 { val: [0; 4] };
        let mut c3 = AlignedArrayu64x4 { val: [0; 4] };

        let w = _mm256_set_epi32(
            twiddle[exp * 3].val as i32,
            twiddle[0].val as i32,
            twiddle[exp].val as i32,
            twiddle[0].val as i32,
            twiddle[exp * 2].val as i32,
            twiddle[0].val as i32,
            Mint::one().val as i32,
            Mint::one().val as i32,
        );
        for top in (0..deg).step_by(8) {
            c0.val[0] = a[top].val as u64;
            c1.val[0] = a[top + 2].val as u64;
            c2.val[0] = a[top + 4].val as u64;
            c3.val[0] = a[top + 6].val as u64;
            c0.val[1] = a[top + 1].val as u64;
            c1.val[1] = a[top + 3].val as u64;
            c2.val[1] = a[top + 5].val as u64;
            c3.val[1] = a[top + 7].val as u64;

            let c0 = _mm_load_si128(c0.val.as_ptr() as *const _);
            let c1 = _mm_load_si128(c1.val.as_ptr() as *const _);
            let c2 = _mm_load_si128(c2.val.as_ptr() as *const _);
            let c3 = _mm_load_si128(c3.val.as_ptr() as *const _);

            let (c0, c1, c2, c3) = radix_4_innerx4(
                _mm256_castsi128_si256(c0),
                _mm256_castsi128_si256(c1),
                _mm256_castsi128_si256(c2),
                _mm256_castsi128_si256(c3),
                modulo,
                modulo_inv,
                prim_root,
            );

            // c0       = [c00, 0, c10, 0, 0, 0, 0, 0], c1 = [c01, 0, c11, 0, 0, 0, 0, 0]
            // c01      = [c00, 0, c10, 0, c01, 0, c11, 0]
            let c01 = _mm256_set_m128i(_mm256_castsi256_si128(c1), _mm256_castsi256_si128(c0));
            // c2       = [c02, 0, c12, 0, 0, 0, 0, 0], c3 = [c03, 0, c13, 0, 0, 0, 0, 0]
            // c23      = [c02, 0, c12, 0, c03, 0, c13, 0]
            let c23 = _mm256_set_m128i(_mm256_castsi256_si128(c3), _mm256_castsi256_si128(c2));
            // c0123    = [c00, c02, c10, c12, c01, c03, c11, c13]
            let c0123 = _mm256_unpacklo_epi64(_mm256_unpacklo_epi32(c01, c23), _mm256_unpackhi_epi32(c01, c23));
            // c0123    = [c00, c10, c02, c12, c01, c11, c03, c13]
            let c0123 = _mm256_shuffle_epi32(c0123, 0b11_01_10_00);
            let c0123 = montgomery_multiplication_u32x8(w, c0123, modulo, modulo_inv);

            _mm256_storeu_si256(a[top..top + 8].as_mut_ptr() as *mut _, c0123);
        }
    } else if offset == 4 {
        let mut w02 = AlignedArrayu32x8 { val: [Mint::one().val; 8] };
        let mut w13 = AlignedArrayu32x8 { val: [0; 8] };
        for (i, exp_now) in (0..4).map(|i| (i, (i * exp) & (deg - 1))) {
            w13.val[i] = twiddle[exp_now].val;
            w02.val[i + 4] = twiddle[exp_now * 2].val;
            w13.val[i + 4] = twiddle[exp_now * 3].val;
        }
        let w02 = _mm256_load_si256(w02.val.as_mut_ptr() as *mut _);
        let w13 = _mm256_load_si256(w13.val.as_mut_ptr() as *mut _);

        for a in a.chunks_exact_mut(16) {
            let c0 = _mm_loadu_si128(a[0..4].as_ptr() as *const _);
            let c1 = _mm_loadu_si128(a[4..8].as_ptr() as *const _);
            let c2 = _mm_loadu_si128(a[8..12].as_ptr() as *const _);
            let c3 = _mm_loadu_si128(a[12..16].as_ptr() as *const _);

            let (c0, c1, c2, c3) = radix_4_innerx8(
                _mm256_castsi128_si256(c0),
                _mm256_castsi128_si256(c1),
                _mm256_castsi128_si256(c2),
                _mm256_castsi128_si256(c3),
                modulo,
                modulo_inv,
                prim_root,
            );

            {
                let c02 = _mm256_set_m128i(_mm256_castsi256_si128(c2), _mm256_castsi256_si128(c0));
                let c02 = montgomery_multiplication_u32x8(w02, c02, modulo, modulo_inv);
                _mm256_storeu_si256(a[..8].as_mut_ptr() as *mut _, c02);
            }

            {
                let c13 = _mm256_set_m128i(_mm256_castsi256_si128(c3), _mm256_castsi256_si128(c1));
                let c13 = montgomery_multiplication_u32x8(w13, c13, modulo, modulo_inv);
                _mm256_storeu_si256(a[8..16].as_mut_ptr() as *mut _, c13);
            }
        }
    } else {
        let mut w1 = AlignedArrayu32x8 { val: [0; 8] };
        let mut w2 = AlignedArrayu32x8 { val: [0; 8] };
        let mut w3 = AlignedArrayu32x8 { val: [0; 8] };

        for top in (0..deg).step_by(width) {
            let mut exp_now = 0;
            for base in (top..top + offset).step_by(8) {
                let c0 = _mm256_loadu_si256(a[base..base + 8].as_ptr() as *const _);
                let c1 = _mm256_loadu_si256(a[base + offset..base + offset + 8].as_ptr() as *const _);
                let c2 = _mm256_loadu_si256(a[base + offset * 2..base + offset * 2 + 8].as_ptr() as *const _);
                let c3 = _mm256_loadu_si256(a[base + offset * 3..base + offset * 3 + 8].as_ptr() as *const _);

                let (c0, c1, c2, c3) = radix_4_innerx8(c0, c1, c2, c3, modulo, modulo_inv, prim_root);
                for i in 0..8 {
                    w1.val[i] = twiddle[exp_now].val;
                    w2.val[i] = twiddle[exp_now * 2].val;
                    w3.val[i] = twiddle[exp_now * 3].val;
                    exp_now = (exp_now + exp) & (deg - 1);
                }

                let (w1, w2, w3) = (
                    _mm256_load_si256(w1.val.as_ptr() as *const _),
                    _mm256_load_si256(w2.val.as_ptr() as *const _),
                    _mm256_load_si256(w3.val.as_ptr() as *const _),
                );

                let (c1, c2, c3) = (
                    montgomery_multiplication_u32x8(w1, c1, modulo, modulo_inv),
                    montgomery_multiplication_u32x8(w2, c2, modulo, modulo_inv),
                    montgomery_multiplication_u32x8(w3, c3, modulo, modulo_inv),
                );

                _mm256_storeu_si256(a[base..base + 8].as_mut_ptr() as *mut _, c0);
                _mm256_storeu_si256(a[base + offset * 2..base + offset * 2 + 8].as_mut_ptr() as *mut _, c1);
                _mm256_storeu_si256(a[base + offset..base + offset + 8].as_mut_ptr() as *mut _, c2);
                _mm256_storeu_si256(a[base + offset * 3..base + offset * 3 + 8].as_mut_ptr() as *mut _, c3);
            }
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn gentleman_sande_radix_4_butterfly_montgomery_modint_avx2(deg: usize, log: usize, a: &mut [Mint], cache: &FftCache<Mint>) {
    let twiddle = cache.twiddle_factors();
    assert_eq!(twiddle[(twiddle.len() - 1) >> 2], cache.prim_root(2));
    for i in (0..log).step_by(2) {
        let width = deg >> i;
        if i + 1 == log {
            radix_2_kernel_gentleman_sande_avx2(width, a);
        } else {
            radix_4_kernel_gentleman_sande_avx2(deg, width, a, twiddle);
        }
    }
}

#[allow(dead_code)]
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn gentleman_sande_radix_4_butterfly_inv_montgomery_modint_avx2(deg: usize, log: usize, a: &mut [Mint], cache: &FftCache<Mint>) {
    let twiddle = cache.twiddle_factors_inv();
    for i in (0..log).step_by(2) {
        let width = deg >> i;
        if i + 1 == log {
            radix_2_kernel_gentleman_sande_avx2(width, a);
        } else {
            radix_4_kernel_gentleman_sande_avx2(deg, width, a, twiddle);
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn radix_2_kernel_cooley_tukey_avx2(width: usize, a: &mut [Mint]) {
    // offset = width >> 1;
    assert_eq!(width >> 1, 1);
    for a in a.chunks_exact_mut(2) {
        let c1 = a[1];
        a[1] = a[0] - c1;
        a[0] += c1;
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn radix_4_kernel_cooley_tukey_avx2(deg: usize, width: usize, a: &mut [Mint], twiddle: &[Mint]) {
    let log = width.trailing_zeros();
    let exp = deg >> log;

    // Constants for Montgomery Operation
    let modulo_inv = _mm256_set1_epi32(Mod998244353::MOD_INV as i32);
    let modulo = _mm256_set1_epi32(Mod998244353::MOD as i32);
    let prim_root = _mm256_set1_epi32(twiddle[deg >> 2].val as i32);

    let offset = width >> 2;
    if offset == 1 {
        let prim_root = twiddle[(twiddle.len() - 1) >> 2];
        for a in a.chunks_exact_mut(4) {
            let (c0, c1, c2, c3) = (a[0], a[2], a[1], a[3]);
            let (c0, c1, c2, c3) = {
                let c0pc2 = c0 + c2;
                let c0mc2 = c0 - c2;
                let c1pc3 = c1 + c3;
                let c1mc3 = c1 - c3;
                let c1mc3im = c1mc3 * prim_root;
                (c0pc2 + c1pc3, c0mc2 + c1mc3im, c0pc2 - c1pc3, c0mc2 - c1mc3im)
            };
            a[0] = c0;
            a[1] = c1;
            a[2] = c2;
            a[3] = c3;
        }
    } else if offset == 2 {
        let w = _mm256_set_epi32(
            twiddle[exp * 3].val as i32,
            twiddle[0].val as i32,
            twiddle[exp].val as i32,
            twiddle[0].val as i32,
            twiddle[exp * 2].val as i32,
            twiddle[0].val as i32,
            Mint::one().val as i32,
            Mint::one().val as i32,
        );

        for a in a.chunks_exact_mut(8) {
            let c0213 = _mm256_loadu_si256(a.as_ptr() as *const _);
            let c0213 = montgomery_multiplication_u32x8(w, c0213, modulo, modulo_inv);

            let (c0, c1, c2, c3) = (
                _mm256_shuffle_epi32(c0213, 0b11_01_10_00),
                _mm256_shuffle_epi32(_mm256_castsi128_si256(_mm256_extracti128_si256(c0213, 1)), 0b11_01_10_00),
                _mm256_shuffle_epi32(c0213, 0b01_11_00_10),
                _mm256_shuffle_epi32(_mm256_castsi128_si256(_mm256_extracti128_si256(c0213, 1)), 0b01_11_00_10),
            );

            let (c0, c1, c2, c3) = radix_4_innerx4(c0, c1, c2, c3, modulo, modulo_inv, prim_root);

            // c0       = [c00, 0, c10, 0, 0, 0, 0, 0], c2 = [c02, 0, c12, 0, 0, 0, 0, 0]
            // c02      = [c00, 0, c10, 0, c02, 0, c12, 0]
            let c02 = _mm256_set_m128i(_mm256_castsi256_si128(c2), _mm256_castsi256_si128(c0));
            // c1       = [c01, 0, c11, 0, 0, 0, 0, 0], c3 = [c03, 0, c13, 0, 0, 0, 0, 0]
            // c13      = [c01, 0, c11, 0, c03, 0, c13, 0]
            let c13 = _mm256_set_m128i(_mm256_castsi256_si128(c3), _mm256_castsi256_si128(c1));
            // c0123    = [c00, c01, c10, c11, c02, c03, c12, c13]
            let c0123 = _mm256_unpacklo_epi64(_mm256_unpacklo_epi32(c02, c13), _mm256_unpackhi_epi32(c02, c13));
            // c0123    = [c00, c10, c01, c11, c02, c12, c03, c13]
            let c0123 = _mm256_shuffle_epi32(c0123, 0b11_01_10_00);

            _mm256_storeu_si256(a.as_mut_ptr() as *mut _, c0123);
        }
    } else if offset == 4 {
        let mut w02 = AlignedArrayu32x8 { val: [Mint::one().val; 8] };
        let mut w13 = AlignedArrayu32x8 { val: [0; 8] };
        for (i, exp_now) in (0..4).map(|i| (i, (i * exp) & (deg - 1))) {
            w13.val[i] = twiddle[exp_now].val;
            w02.val[i + 4] = twiddle[exp_now * 2].val;
            w13.val[i + 4] = twiddle[exp_now * 3].val;
        }
        let w02 = _mm256_load_si256(w02.val.as_mut_ptr() as *mut _);
        let w13 = _mm256_load_si256(w13.val.as_mut_ptr() as *mut _);

        for a in a.chunks_exact_mut(16) {
            let c02 = _mm256_loadu_si256(a[0..8].as_ptr() as *const _);
            let c13 = _mm256_loadu_si256(a[8..].as_ptr() as *const _);

            let c02 = montgomery_multiplication_u32x8(w02, c02, modulo, modulo_inv);
            let c13 = montgomery_multiplication_u32x8(w13, c13, modulo, modulo_inv);

            let (c0, c1, c2, c3) = (
                _mm256_castsi256_si128(c02),
                _mm256_castsi256_si128(c13),
                _mm256_extracti128_si256(c02, 1),
                _mm256_extracti128_si256(c13, 1),
            );

            let (c0, c1, c2, c3) = radix_4_innerx8(
                _mm256_castsi128_si256(c0),
                _mm256_castsi128_si256(c1),
                _mm256_castsi128_si256(c2),
                _mm256_castsi128_si256(c3),
                modulo,
                modulo_inv,
                prim_root,
            );

            _mm256_storeu_si256(a[0..8].as_mut_ptr() as *mut _, _mm256_set_m128i(_mm256_castsi256_si128(c1), _mm256_castsi256_si128(c0)));
            _mm256_storeu_si256(a[8..].as_mut_ptr() as *mut _, _mm256_set_m128i(_mm256_castsi256_si128(c3), _mm256_castsi256_si128(c2)));
        }
    } else {
        let mut w1 = AlignedArrayu32x8 { val: [0; 8] };
        let mut w2 = AlignedArrayu32x8 { val: [0; 8] };
        let mut w3 = AlignedArrayu32x8 { val: [0; 8] };
        for top in (0..deg).step_by(width) {
            let mut exp_now = 0;
            for base in (top..top + offset).step_by(8) {
                let c0 = _mm256_loadu_si256(a[base..base + 8].as_ptr() as *const _);
                let c1 = _mm256_loadu_si256(a[base + offset * 2..base + offset * 2 + 8].as_ptr() as *const _);
                let c2 = _mm256_loadu_si256(a[base + offset..base + offset + 8].as_ptr() as *const _);
                let c3 = _mm256_loadu_si256(a[base + offset * 3..base + offset * 3 + 8].as_ptr() as *const _);

                for i in 0..8 {
                    w1.val[i] = twiddle[exp_now].val;
                    w2.val[i] = twiddle[exp_now * 2].val;
                    w3.val[i] = twiddle[exp_now * 3].val;
                    exp_now = (exp_now + exp) & (deg - 1);
                }
                let (w1, w2, w3) = (
                    _mm256_load_si256(w1.val.as_ptr() as *const _),
                    _mm256_load_si256(w2.val.as_ptr() as *const _),
                    _mm256_load_si256(w3.val.as_ptr() as *const _),
                );

                let c1 = montgomery_multiplication_u32x8(w1, c1, modulo, modulo_inv);
                let c2 = montgomery_multiplication_u32x8(w2, c2, modulo, modulo_inv);
                let c3 = montgomery_multiplication_u32x8(w3, c3, modulo, modulo_inv);

                let (c0, c1, c2, c3) = radix_4_innerx8(c0, c1, c2, c3, modulo, modulo_inv, prim_root);

                _mm256_storeu_si256(a[base..base + 8].as_mut_ptr() as *mut _, c0);
                _mm256_storeu_si256(a[base + offset..base + offset + 8].as_mut_ptr() as *mut _, c1);
                _mm256_storeu_si256(a[base + offset * 2..base + offset * 2 + 8].as_mut_ptr() as *mut _, c2);
                _mm256_storeu_si256(a[base + offset * 3..base + offset * 3 + 8].as_mut_ptr() as *mut _, c3);
            }
        }
    }
}

#[allow(dead_code)]
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn cooley_tukey_radix_4_butterfly_montgomery_modint_avx2(deg: usize, log: usize, a: &mut [Mint], cache: &FftCache<Mint>) {
    let twiddle = cache.twiddle_factors();
    let start = if log & 1 != 0 {
        radix_2_kernel_cooley_tukey_avx2(1 << 1, a);
        1
    } else {
        0
    };
    for i in (start..log).step_by(2) {
        let width = 1 << (i + 2);
        radix_4_kernel_cooley_tukey_avx2(deg, width, a, twiddle);
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2(deg: usize, log: usize, a: &mut [Mint], cache: &FftCache<Mint>) {
    let twiddle = cache.twiddle_factors_inv();
    assert_eq!(twiddle[(twiddle.len() - 1) >> 2], cache.prim_root_inv(2));
    let start = if log & 1 != 0 {
        radix_2_kernel_cooley_tukey_avx2(1 << 1, a);
        1
    } else {
        0
    };
    for i in (start..log).step_by(2) {
        let width = 1 << (i + 2);
        radix_4_kernel_cooley_tukey_avx2(deg, width, a, twiddle);
    }
}

#[cfg(test)]
mod tests_gentleman_sande {
    use super::super::common::bit_reverse;
    use super::super::FftCache;
    use super::{gentleman_sande_radix_4_butterfly_inv_montgomery_modint_avx2, gentleman_sande_radix_4_butterfly_montgomery_modint_avx2};
    use modint::{Mod998244353, MontgomeryModint};

    type MontMint998244353 = MontgomeryModint<Mod998244353>;

    macro_rules! impl_fft_inner {
        ( $t:ty, $butterfly:ident, $deg:ident, $log:ident, $a:ident, $cache:ident, $epilogue:expr ) => {{
            unsafe {
                $butterfly($deg, $log, $a, &($cache));
            }
            bit_reverse($deg, $log, $a);
            $epilogue($deg, $a);
        }};
    }

    macro_rules! impl_fft_template {
        ( $t:ty, $fname:ident, $butterfly:ident, $inner:expr ) => {
            pub fn $fname(a: &mut [$t]) {
                let deg = a.len();
                let log = deg.trailing_zeros() as usize;
                debug_assert_eq!(a.len(), 1 << log);
                let cache = FftCache::<$t>::new(log);
                impl_fft_inner!($t, $butterfly, deg, log, a, cache, $inner);
            }
        };
    }

    macro_rules! impl_fft {
        ( $t:ty, $fname:ident, $butterfly:ident, $fname_inv:ident, $butterfly_inv:ident, $inner_inv:expr) => {
            impl_fft_template!($t, $fname, $butterfly, {});
            impl_fft_template!($t, $fname_inv, $butterfly_inv, $inner_inv);
        };
    }

    macro_rules! impl_fft_all_radix {
        ( $t:ty, $rad8:ident, $butterfly8:ident, $rad8inv:ident, $butterfly8inv:ident, $inner_inv:expr) => {
            impl_fft!($t, $rad8, $butterfly8, $rad8inv, $butterfly8inv, $inner_inv);
        };
    }

    impl_fft_all_radix!(
        MontMint998244353,
        fft_gentleman_sande_radix_4_montgomery_modint,
        gentleman_sande_radix_4_butterfly_montgomery_modint_avx2,
        ifft_gentleman_sande_radix_4_montgomery_modint,
        gentleman_sande_radix_4_butterfly_inv_montgomery_modint_avx2,
        |deg: usize, a: &mut [MontMint998244353]| {
            let inv = MontMint998244353::new(deg as u32).inv();
            a.iter_mut().for_each(|c| *c *= inv)
        }
    );

    const N: u32 = 1 << 4;

    #[test]
    fn gentleman_sande_radix_4_montgomery_modint_test() {
        let data: Vec<MontMint998244353> = (1..=N).map(|v| MontMint998244353::new(v)).collect();
        let mut data1 = data.clone();
        fft_gentleman_sande_radix_4_montgomery_modint(&mut data1);
        ifft_gentleman_sande_radix_4_montgomery_modint(&mut data1);
        assert_eq!(data, data1);

        let data = [
            MontMint998244353::from(817609646),
            MontMint998244353::from(512965573),
            MontMint998244353::zero(),
            MontMint998244353::zero(),
        ];
        let mut data1 = data.clone();
        fft_gentleman_sande_radix_4_montgomery_modint(&mut data1);
        ifft_gentleman_sande_radix_4_montgomery_modint(&mut data1);
        assert_eq!(data, data1);
    }
}

#[cfg(test)]
mod tests_cooley_tukey {
    use super::super::common::bit_reverse;
    use super::super::FftCache;
    use super::{cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2, cooley_tukey_radix_4_butterfly_montgomery_modint_avx2};
    use modint::{Mod998244353, MontgomeryModint};

    type MontMint998244353 = MontgomeryModint<Mod998244353>;

    macro_rules! impl_fft_inner {
        ( $t:ty, $butterfly:ident, $deg:ident, $log:ident, $a:ident, $cache:ident, $epilogue:expr ) => {{
            unsafe {
                $butterfly($deg, $log, $a, &($cache));
            }
            $epilogue($deg, $a);
        }};
    }

    macro_rules! impl_fft_template {
        ( $t:ty, $fname:ident, $butterfly:ident, $inner:expr ) => {
            pub fn $fname(a: &mut [$t]) {
                let deg = a.len();
                let log = deg.trailing_zeros() as usize;
                debug_assert_eq!(a.len(), 1 << log);
                bit_reverse(deg, log, a);
                let cache = FftCache::<$t>::new(log);
                impl_fft_inner!($t, $butterfly, deg, log, a, cache, $inner)
            }
        };
    }

    macro_rules! impl_fft {
        ( $t:ty, $fname:ident, $butterfly:ident, $fname_inv:ident, $butterfly_inv:ident, $inner_inv:expr) => {
            impl_fft_template!($t, $fname, $butterfly, {});
            impl_fft_template!($t, $fname_inv, $butterfly_inv, $inner_inv);
        };
    }

    macro_rules! impl_fft_all_radix {
        ( $t:ty, $rad8:ident, $butterfly8:ident, $rad8inv:ident, $butterfly8inv:ident, $inner_inv:expr) => {
            impl_fft!($t, $rad8, $butterfly8, $rad8inv, $butterfly8inv, $inner_inv);
        };
    }

    impl_fft_all_radix!(
        MontMint998244353,
        fft_cooley_tukey_radix_4_montgomery_modint_avx2,
        cooley_tukey_radix_4_butterfly_montgomery_modint_avx2,
        ifft_cooley_tukey_radix_4_montgomery_modint_avx2,
        cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2,
        |deg: usize, a: &mut [MontMint998244353]| {
            let inv = MontMint998244353::new(deg as u32).inv();
            a.iter_mut().for_each(|c| *c *= inv)
        }
    );

    const N: u32 = 1 << 3;

    #[test]
    fn cooley_tukey_radix_8_montgomery_modint_test() {
        let data: Vec<MontMint998244353> = (1..=N).map(|v| MontMint998244353::new(v)).collect();
        let mut data1 = data.clone();
        fft_cooley_tukey_radix_4_montgomery_modint_avx2(&mut data1);
        ifft_cooley_tukey_radix_4_montgomery_modint_avx2(&mut data1);
        assert_eq!(data, data1);

        let data = [
            MontMint998244353::from(817609646),
            MontMint998244353::from(512965573),
            MontMint998244353::zero(),
            MontMint998244353::zero(),
        ];
        let mut data1 = data.clone();
        fft_cooley_tukey_radix_4_montgomery_modint_avx2(&mut data1);
        ifft_cooley_tukey_radix_4_montgomery_modint_avx2(&mut data1);
        assert_eq!(data, data1);
    }
}
