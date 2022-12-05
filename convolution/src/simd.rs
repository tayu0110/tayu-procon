use super::FftCache;
use modint::{Mod998244353, Modulo, MontgomeryModint};
#[cfg(target_arch = "x86")]
use std::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{
    __m256i, _mm256_add_epi32, _mm256_add_epi64, _mm256_alignr_epi8, _mm256_and_si256, _mm256_blendv_epi8, _mm256_castsi256_si128, _mm256_cmpgt_epi32, _mm256_cvtepi32_epi64,
    _mm256_mul_epu32, _mm256_mullo_epi32, _mm256_permute2x128_si256, _mm256_permutevar8x32_epi32, _mm256_set1_epi32, _mm256_set1_epi64x, _mm256_set_epi32, _mm256_set_epi64x,
    _mm256_setzero_si256, _mm256_store_si256, _mm256_sub_epi32, _mm_loadu_si128, _mm_storeu_si128,
};

type Mint = MontgomeryModint<Mod998244353<u32>, u32>;
type Radix4Inner<T> = fn(T, T, T, T, &FftCache<T>) -> (T, T, T, T);

#[repr(C, align(32))]
struct AlignedArrayu32x8 {
    val: [u32; 8],
}

#[inline]
#[target_feature(enable = "avx2")]
// ws: [(0, w0), (0, w1), (0, w2), (0, w3)]
// cs: [(0, c0), (0, c1), (0, c2), (0, c3)]
//  -> [0, w0c0, 0, w1c1, 0, w2c2, 0, w3c3]
unsafe fn montgomery_multiplication_u32x4(ws: __m256i, cs: __m256i, modulo: __m256i, mod_inv: __m256i, zero: __m256i) -> __m256i {
    // Parallelization of Montgomery Multiplication
    // ws    = [(0, w0), (0, w1), (0, w2), (0, w3)], cs = [(0, c0), (0, c1), (0, c2), (0, c3)]
    // t     = [(w0 * c0 as i64), (w1 * c1 as i64), (w2 * c2 as i64), (w3 * c3 as i64)]
    //       = [(w0c0hi, w0c0lo), (w1c1hi, w1c1lo), (w2c2hi, w2c2lo), (w3c3hi, w3c3lo)]
    // tmi   = [(w0c0hi.wrap_mul(modinv), w0c0lo.wrap_mul(modinv)), (w1c1hi.wrap_mul(modinv), w1c1lo.wrap_mul(modinv)),
    //          (w2c2hi.wrap_mul(modinv), w2c2lo.wrap_mul(modinv)), (w3c3hi.wrap_mul(modinv), w3c3lo.wrap_mul(modinv))]
    // u     = [(w0c0lo.wrap_mul(modinv) * mod as i64), (w1c1lo.wrap_mul(modinv) * mod as i64),
    //          (w2c2lo.wrap_mul(modinv) * mod as i64), (w3c3lo.wrap_mul(modinv) * mod as i64)]
    // c     = [t + (w0c0lo.wrap_mul(modinv) * mod as i64), t + (w1c1lo.wrap_mul(modinv) * mod as i64),
    //          t + (w2c2lo.wrap_mul(modinv) * mod as i64), t + (w3c3lo.wrap_mul(modinv) * mod as i64)]
    // MR(t) = (t as u64 + (((wxcxlo * modinv) & mask) * mod as u64)) >> 32 = c
    //      if c[i] >= mod then return c[i] - mod else return c[i]
    let t = _mm256_mul_epu32(ws, cs);
    let tmi = _mm256_mullo_epi32(t, mod_inv);
    let u = _mm256_mul_epu32(tmi, modulo);
    let c = _mm256_add_epi64(t, u);
    // c_neg[i] = c[i] - mod
    let c_neg = _mm256_sub_epi32(c, modulo);
    // if (c_neg[i] < 0) == (c[i] < mod) then
    //      mask[i] == 0xFFFF
    // else
    //      mask[i] == 0x0000
    let mask = _mm256_cmpgt_epi32(zero, c_neg);
    // if mask[i] == 0xFFFF then
    //      res[i] = c
    // else
    //      res[i] = c_neg
    let res = _mm256_blendv_epi8(c_neg, c, mask);
    _mm256_shift_rightx4byte(res)
}

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn _mm256_add_mod_epi32(a: __m256i, b: __m256i, modulo: __m256i, zero: __m256i) -> __m256i {
    let c = _mm256_add_epi32(a, b);
    let c_neg = _mm256_sub_epi32(c, modulo);
    let mask = _mm256_cmpgt_epi32(zero, c_neg);
    _mm256_blendv_epi8(c_neg, c, mask)
}

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn _mm256_sub_mod_epi32(a: __m256i, b: __m256i, modulo: __m256i, zero: __m256i) -> __m256i {
    let c_neg = _mm256_sub_epi32(a, b);
    let c = _mm256_add_epi32(c_neg, modulo);
    let mask = _mm256_cmpgt_epi32(zero, c_neg);
    _mm256_blendv_epi8(c_neg, c, mask)
}

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn _mm256_shift_rightx4byte(a: __m256i) -> __m256i {
    let mask = _mm256_permute2x128_si256(a, a, 0x81);
    _mm256_alignr_epi8(mask, a, 4)
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
unsafe fn radix_4_inner_avx2(
    c0: __m256i,
    c1: __m256i,
    c2: __m256i,
    c3: __m256i,
    modulo: __m256i,
    mod_inv: __m256i,
    zero: __m256i,
    prim_root: __m256i,
) -> (__m256i, __m256i, __m256i, __m256i) {
    let c0pc2 = _mm256_add_mod_epi32(c0, c2, modulo, zero);
    let c0mc2 = _mm256_sub_mod_epi32(c0, c2, modulo, zero);
    let c1pc3 = _mm256_add_mod_epi32(c1, c3, modulo, zero);
    let c1mc3 = _mm256_sub_mod_epi32(c1, c3, modulo, zero);
    let c1mc3im = montgomery_multiplication_u32x4(c1mc3, prim_root, modulo, mod_inv, zero);
    (
        _mm256_add_mod_epi32(c0pc2, c1pc3, modulo, zero),
        _mm256_add_mod_epi32(c0mc2, c1mc3im, modulo, zero),
        _mm256_sub_mod_epi32(c0pc2, c1pc3, modulo, zero),
        _mm256_sub_mod_epi32(c0mc2, c1mc3im, modulo, zero),
    )
}

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn radix_2_kernel_gentleman_sande_avx2(deg: usize, width: usize, a: &mut [Mint], twiddle: &[Mint]) {
    let offset = width >> 1;
    let log = width.trailing_zeros();
    let exp_base = (deg >> log) & (deg - 1);
    let mut exp = exp_base;
    if offset == 1 {
        for top in (0..deg).step_by(width) {
            let (c0, c1) = (a[top], a[top + offset]);
            a[top] = c0 + c1;
            a[top + offset] = c0 - c1;
        }
    } else {
        for top in (0..deg).step_by(width) {
            let (c0, c1) = (a[top], a[top + offset]);
            a[top] = c0 + c1;
            a[top + offset] = c0 - c1;
            for base in top + 1..top + offset {
                let (c0, c1) = (a[base], a[base + offset]);
                let (c0, c1) = (c0 + c1, c0 - c1);

                a[base] = c0;
                a[base + offset] = c1 * twiddle[exp];
                exp = (exp + exp_base) & (deg - 1);
            }
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn radix_4_kernel_gentleman_sande_avx2(deg: usize, width: usize, a: &mut [Mint], cache: &FftCache<Mint>, twiddle: &[Mint], radix4_inner: Radix4Inner<Mint>) {
    let log = width.trailing_zeros();

    let exp = (deg >> log) as i32;
    let exp_base = _mm256_set_epi32(exp * 3, exp * 2, exp, 0, 0, 0, 0, 0);
    let exp_mask = _mm256_set1_epi32(deg as i32 - 1);
    let exp_diff = _mm256_set_epi32(exp * 6, exp * 4, exp * 2, 0, exp * 6, exp * 4, exp * 2, 0);
    let mut exp_now = AlignedArrayu32x8 { val: [0u32; 8] };

    // Constants for Montgomery Operation
    let modulo_inv = _mm256_set1_epi32(Mod998244353::<u32>::montgomery_constant_modulo_inv() as i32);
    let modulo = _mm256_set1_epi32(Mod998244353::<u32>::modulo() as i32);
    let all_zero = _mm256_setzero_si256();
    let mut dest = AlignedArrayu32x8 { val: [0u32; 8] };
    let prim_root = _mm256_set1_epi64x(twiddle[deg >> 2].val_montgomery_expression() as i64);

    let perm_mask = _mm256_set_epi32(7, 5, 3, 1, 6, 4, 2, 0);

    let offset = width >> 2;
    if offset == 1 {
        for top in (0..deg).step_by(width) {
            let (id0, id1, id2, id3) = (top, top + offset, top + offset * 2, top + offset * 3);
            let (c0, c1, c2, c3) = (a[id0], a[id1], a[id2], a[id3]);
            let (c0, c1, c2, c3) = radix4_inner(c0, c1, c2, c3, cache);
            a[id0] = c0;
            a[id2] = c1;
            a[id1] = c2;
            a[id3] = c3;
        }
    } else if offset == 2 {
        _mm256_store_si256(exp_now.val.as_mut_ptr() as *mut _, exp_base);
        let (w01, w02, w03) = (twiddle[exp_now.val[1] as usize], twiddle[exp_now.val[2] as usize], twiddle[exp_now.val[3] as usize]);
        let (w11, w12, w13) = (twiddle[exp_now.val[5] as usize], twiddle[exp_now.val[6] as usize], twiddle[exp_now.val[7] as usize]);

        let w1 = _mm256_set_epi64x(0, 0, w11.val_montgomery_expression() as i64, w01.val_montgomery_expression() as i64);
        let w2 = _mm256_set_epi64x(0, 0, w12.val_montgomery_expression() as i64, w02.val_montgomery_expression() as i64);
        let w3 = _mm256_set_epi64x(0, 0, w13.val_montgomery_expression() as i64, w03.val_montgomery_expression() as i64);
        for top in (0..deg).step_by(width) {
            let (id00, id01, id02, id03) = (top, top + offset, top + offset * 2, top + offset * 3);
            let (id10, id11, id12, id13) = (top + 1, top + 1 + offset, top + 1 + offset * 2, top + 1 + offset * 3);

            let (c00, c01, c02, c03) = (a[id00], a[id01], a[id02], a[id03]);
            let (c10, c11, c12, c13) = (a[id10], a[id11], a[id12], a[id13]);

            let c0 = _mm256_set_epi64x(0, 0, c10.val_montgomery_expression() as i64, c00.val_montgomery_expression() as i64);
            let c1 = _mm256_set_epi64x(0, 0, c11.val_montgomery_expression() as i64, c01.val_montgomery_expression() as i64);
            let c2 = _mm256_set_epi64x(0, 0, c12.val_montgomery_expression() as i64, c02.val_montgomery_expression() as i64);
            let c3 = _mm256_set_epi64x(0, 0, c13.val_montgomery_expression() as i64, c03.val_montgomery_expression() as i64);

            let (c0, c1, c2, c3) = radix_4_inner_avx2(c0, c1, c2, c3, modulo, modulo_inv, all_zero, prim_root);

            let c1 = montgomery_multiplication_u32x4(w1, c1, modulo, modulo_inv, all_zero);
            let c2 = montgomery_multiplication_u32x4(w2, c2, modulo, modulo_inv, all_zero);
            let c3 = montgomery_multiplication_u32x4(w3, c3, modulo, modulo_inv, all_zero);

            _mm256_store_si256(dest.val.as_mut_ptr() as *mut _, c0);
            a[id00] = Mint::from_montgomery_expression(dest.val[0]);
            a[id10] = Mint::from_montgomery_expression(dest.val[2]);

            _mm256_store_si256(dest.val.as_mut_ptr() as *mut _, c1);
            a[id02] = Mint::from_montgomery_expression(dest.val[0]);
            a[id12] = Mint::from_montgomery_expression(dest.val[2]);

            _mm256_store_si256(dest.val.as_mut_ptr() as *mut _, c2);
            a[id01] = Mint::from_montgomery_expression(dest.val[0]);
            a[id11] = Mint::from_montgomery_expression(dest.val[2]);

            _mm256_store_si256(dest.val.as_mut_ptr() as *mut _, c3);
            a[id03] = Mint::from_montgomery_expression(dest.val[0]);
            a[id13] = Mint::from_montgomery_expression(dest.val[2]);
        }
    } else {
        for top in (0..deg).step_by(width) {
            let mut exp_cache = exp_base.clone();
            for base in (top..top + offset).step_by(4) {
                let c0 = _mm256_cvtepi32_epi64(_mm_loadu_si128(a[base..base + 4].as_ptr() as *const _));
                let c1 = _mm256_cvtepi32_epi64(_mm_loadu_si128(a[base + offset..base + offset + 4].as_ptr() as *const _));
                let c2 = _mm256_cvtepi32_epi64(_mm_loadu_si128(a[base + offset * 2..base + offset * 2 + 4].as_ptr() as *const _));
                let c3 = _mm256_cvtepi32_epi64(_mm_loadu_si128(a[base + offset * 3..base + offset * 3 + 4].as_ptr() as *const _));

                let (c0, c1, c2, c3) = radix_4_inner_avx2(c0, c1, c2, c3, modulo, modulo_inv, all_zero, prim_root);

                // c0 is no longer used, so STORE and cut scope here.
                _mm_storeu_si128(a[base..base + 4].as_mut_ptr() as *mut _, _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(c0, perm_mask)));

                _mm256_store_si256(exp_now.val.as_mut_ptr() as *mut _, exp_cache);
                let (w01, w02, w03) = (twiddle[exp_now.val[1] as usize], twiddle[exp_now.val[2] as usize], twiddle[exp_now.val[3] as usize]);
                let (w11, w12, w13) = (twiddle[exp_now.val[5] as usize], twiddle[exp_now.val[6] as usize], twiddle[exp_now.val[7] as usize]);
                exp_cache = _mm256_add_epi32(exp_cache, exp_diff);
                exp_cache = _mm256_and_si256(exp_cache, exp_mask);

                _mm256_store_si256(exp_now.val.as_mut_ptr() as *mut _, exp_cache);
                let (w21, w22, w23) = (twiddle[exp_now.val[1] as usize], twiddle[exp_now.val[2] as usize], twiddle[exp_now.val[3] as usize]);
                let (w31, w32, w33) = (twiddle[exp_now.val[5] as usize], twiddle[exp_now.val[6] as usize], twiddle[exp_now.val[7] as usize]);
                exp_cache = _mm256_add_epi32(exp_cache, exp_diff);
                exp_cache = _mm256_and_si256(exp_cache, exp_mask);

                {
                    let w1 = _mm256_set_epi64x(
                        w31.val_montgomery_expression() as i64,
                        w21.val_montgomery_expression() as i64,
                        w11.val_montgomery_expression() as i64,
                        w01.val_montgomery_expression() as i64,
                    );
                    let c1 = montgomery_multiplication_u32x4(w1, c1, modulo, modulo_inv, all_zero);
                    _mm_storeu_si128(
                        a[base + offset * 2..base + offset * 2 + 4].as_mut_ptr() as *mut _,
                        _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(c1, perm_mask)),
                    );
                }

                {
                    let w2 = _mm256_set_epi64x(
                        w32.val_montgomery_expression() as i64,
                        w22.val_montgomery_expression() as i64,
                        w12.val_montgomery_expression() as i64,
                        w02.val_montgomery_expression() as i64,
                    );
                    let c2 = montgomery_multiplication_u32x4(w2, c2, modulo, modulo_inv, all_zero);
                    _mm_storeu_si128(
                        a[base + offset..base + offset + 4].as_mut_ptr() as *mut _,
                        _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(c2, perm_mask)),
                    );
                }

                {
                    let w3 = _mm256_set_epi64x(
                        w33.val_montgomery_expression() as i64,
                        w23.val_montgomery_expression() as i64,
                        w13.val_montgomery_expression() as i64,
                        w03.val_montgomery_expression() as i64,
                    );
                    let c3 = montgomery_multiplication_u32x4(w3, c3, modulo, modulo_inv, all_zero);
                    _mm_storeu_si128(
                        a[base + offset * 3..base + offset * 3 + 4].as_mut_ptr() as *mut _,
                        _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(c3, perm_mask)),
                    );
                }
            }
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn gentleman_sande_radix_4_butterfly_montgomery_modint_avx2(deg: usize, log: usize, a: &mut [Mint], cache: &FftCache<Mint>) {
    let twiddle = cache.twiddle_factors();
    for i in (0..log).step_by(2) {
        let width = deg >> i;
        if i + 1 == log {
            radix_2_kernel_gentleman_sande_avx2(deg, width, a, twiddle);
        } else {
            radix_4_kernel_gentleman_sande_avx2(deg, width, a, cache, twiddle, super::common::radix_4_inner_montgomery_modint);
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
            radix_2_kernel_gentleman_sande_avx2(deg, width, a, twiddle);
        } else {
            radix_4_kernel_gentleman_sande_avx2(deg, width, a, cache, twiddle, super::common::radix_4_inv_inner_montgomery_modint);
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
unsafe fn radix_2_kernel_cooley_tukey_avx2(deg: usize, width: usize, a: &mut [Mint], twiddle: &[Mint]) {
    let offset = width >> 1;
    let log = width.trailing_zeros();
    let exp_base = (deg >> log) & (deg - 1);
    let mut exp = exp_base;

    for top in (0..deg).step_by(width) {
        let (c0, c1) = (a[top], a[top + offset]);
        let (c0, c1) = (c0 + c1, c0 - c1);
        a[top] = c0;
        a[top + offset] = c1;
        for base in top + 1..top + offset {
            let (c0, c1) = (a[base], a[base + offset] * twiddle[exp]);
            let (w0, w1) = (c0 + c1, c0 - c1);
            a[base] = w0;
            a[base + offset] = w1;
            exp = (exp + exp_base) & (deg - 1);
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn radix_4_kernel_cooley_tukey_avx2(deg: usize, width: usize, a: &mut [Mint], cache: &FftCache<Mint>, twiddle: &[Mint], radix4_inner: Radix4Inner<Mint>) {
    let log = width.trailing_zeros();
    let offset = width >> 2;

    let exp = (deg >> log) as i32;
    let exp_base = _mm256_set_epi32(exp * 3, exp * 2, exp, 0, 0, 0, 0, 0);
    let exp_mask = _mm256_set1_epi32(deg as i32 - 1);
    let exp_diff = _mm256_set_epi32(exp * 6, exp * 4, exp * 2, 0, exp * 6, exp * 4, exp * 2, 0);
    let mut exp_now = AlignedArrayu32x8 { val: [0u32; 8] };

    // Constants for Montgomery Operation
    let modulo_inv = _mm256_set1_epi32(Mod998244353::<u32>::montgomery_constant_modulo_inv() as i32);
    let modulo = _mm256_set1_epi32(Mod998244353::<u32>::modulo() as i32);
    let all_zero = _mm256_setzero_si256();
    let mut dest = AlignedArrayu32x8 { val: [0u32; 8] };
    let prim_root = _mm256_set1_epi64x(twiddle[deg >> 2].val_montgomery_expression() as i64);

    let perm_mask = _mm256_set_epi32(7, 5, 3, 1, 6, 4, 2, 0);

    if offset == 1 {
        for top in (0..deg).step_by(width) {
            let (c0, c1, c2, c3) = radix4_inner(a[top], a[top + 2], a[top + 1], a[top + 3], cache);
            a[top] = c0;
            a[top + 1] = c1;
            a[top + 2] = c2;
            a[top + 3] = c3;
        }
    } else if offset == 2 {
        _mm256_store_si256(exp_now.val.as_mut_ptr() as *mut _, exp_base);
        let (w01, w02, w03) = (twiddle[exp_now.val[1] as usize], twiddle[exp_now.val[2] as usize], twiddle[exp_now.val[3] as usize]);
        let (w11, w12, w13) = (twiddle[exp_now.val[5] as usize], twiddle[exp_now.val[6] as usize], twiddle[exp_now.val[7] as usize]);

        let w1 = _mm256_set_epi64x(0, 0, w11.val_montgomery_expression() as i64, w01.val_montgomery_expression() as i64);
        let w2 = _mm256_set_epi64x(0, 0, w12.val_montgomery_expression() as i64, w02.val_montgomery_expression() as i64);
        let w3 = _mm256_set_epi64x(0, 0, w13.val_montgomery_expression() as i64, w03.val_montgomery_expression() as i64);

        for top in (0..deg).step_by(width) {
            let (id00, id01, id02, id03) = (top, top + offset, top + offset * 2, top + offset * 3);
            let (id10, id11, id12, id13) = (top + 1, top + 1 + offset, top + 1 + offset * 2, top + 1 + offset * 3);

            let (c00, c01, c02, c03) = (a[id00], a[id02], a[id01], a[id03]);
            let (c10, c11, c12, c13) = (a[id10], a[id12], a[id11], a[id13]);

            let c0 = _mm256_set_epi64x(0, 0, c10.val_montgomery_expression() as i64, c00.val_montgomery_expression() as i64);
            let c1 = _mm256_set_epi64x(0, 0, c11.val_montgomery_expression() as i64, c01.val_montgomery_expression() as i64);
            let c2 = _mm256_set_epi64x(0, 0, c12.val_montgomery_expression() as i64, c02.val_montgomery_expression() as i64);
            let c3 = _mm256_set_epi64x(0, 0, c13.val_montgomery_expression() as i64, c03.val_montgomery_expression() as i64);

            let c1 = montgomery_multiplication_u32x4(w1, c1, modulo, modulo_inv, all_zero);
            let c2 = montgomery_multiplication_u32x4(w2, c2, modulo, modulo_inv, all_zero);
            let c3 = montgomery_multiplication_u32x4(w3, c3, modulo, modulo_inv, all_zero);

            let (c0, c1, c2, c3) = radix_4_inner_avx2(c0, c1, c2, c3, modulo, modulo_inv, all_zero, prim_root);

            _mm256_store_si256(dest.val.as_mut_ptr() as *mut _, c0);
            a[id00] = Mint::from_montgomery_expression(dest.val[0]);
            a[id10] = Mint::from_montgomery_expression(dest.val[2]);

            _mm256_store_si256(dest.val.as_mut_ptr() as *mut _, c1);
            a[id01] = Mint::from_montgomery_expression(dest.val[0]);
            a[id11] = Mint::from_montgomery_expression(dest.val[2]);

            _mm256_store_si256(dest.val.as_mut_ptr() as *mut _, c2);
            a[id02] = Mint::from_montgomery_expression(dest.val[0]);
            a[id12] = Mint::from_montgomery_expression(dest.val[2]);

            _mm256_store_si256(dest.val.as_mut_ptr() as *mut _, c3);
            a[id03] = Mint::from_montgomery_expression(dest.val[0]);
            a[id13] = Mint::from_montgomery_expression(dest.val[2]);
        }
    } else {
        for top in (0..deg).step_by(width) {
            let mut exp_cache = exp_base.clone();
            for base in (top..top + offset).step_by(4) {
                let c0 = _mm256_cvtepi32_epi64(_mm_loadu_si128(a[base..base + 4].as_ptr() as *const _));
                let c1 = _mm256_cvtepi32_epi64(_mm_loadu_si128(a[base + offset * 2..base + offset * 2 + 4].as_ptr() as *const _));
                let c2 = _mm256_cvtepi32_epi64(_mm_loadu_si128(a[base + offset..base + offset + 4].as_ptr() as *const _));
                let c3 = _mm256_cvtepi32_epi64(_mm_loadu_si128(a[base + offset * 3..base + offset * 3 + 4].as_ptr() as *const _));

                _mm256_store_si256(exp_now.val.as_mut_ptr() as *mut _, exp_cache);
                let (w01, w02, w03) = (twiddle[exp_now.val[1] as usize], twiddle[exp_now.val[2] as usize], twiddle[exp_now.val[3] as usize]);
                let (w11, w12, w13) = (twiddle[exp_now.val[5] as usize], twiddle[exp_now.val[6] as usize], twiddle[exp_now.val[7] as usize]);
                exp_cache = _mm256_add_epi32(exp_cache, exp_diff);
                exp_cache = _mm256_and_si256(exp_cache, exp_mask);

                _mm256_store_si256(exp_now.val.as_mut_ptr() as *mut _, exp_cache);
                let (w21, w22, w23) = (twiddle[exp_now.val[1] as usize], twiddle[exp_now.val[2] as usize], twiddle[exp_now.val[3] as usize]);
                let (w31, w32, w33) = (twiddle[exp_now.val[5] as usize], twiddle[exp_now.val[6] as usize], twiddle[exp_now.val[7] as usize]);
                exp_cache = _mm256_add_epi32(exp_cache, exp_diff);
                exp_cache = _mm256_and_si256(exp_cache, exp_mask);

                let c1 = {
                    let w1 = _mm256_set_epi64x(
                        w31.val_montgomery_expression() as i64,
                        w21.val_montgomery_expression() as i64,
                        w11.val_montgomery_expression() as i64,
                        w01.val_montgomery_expression() as i64,
                    );
                    montgomery_multiplication_u32x4(w1, c1, modulo, modulo_inv, all_zero)
                };

                let c2 = {
                    let w2 = _mm256_set_epi64x(
                        w32.val_montgomery_expression() as i64,
                        w22.val_montgomery_expression() as i64,
                        w12.val_montgomery_expression() as i64,
                        w02.val_montgomery_expression() as i64,
                    );
                    montgomery_multiplication_u32x4(w2, c2, modulo, modulo_inv, all_zero)
                };

                let c3 = {
                    let w3 = _mm256_set_epi64x(
                        w33.val_montgomery_expression() as i64,
                        w23.val_montgomery_expression() as i64,
                        w13.val_montgomery_expression() as i64,
                        w03.val_montgomery_expression() as i64,
                    );
                    montgomery_multiplication_u32x4(w3, c3, modulo, modulo_inv, all_zero)
                };

                let (c0, c1, c2, c3) = radix_4_inner_avx2(c0, c1, c2, c3, modulo, modulo_inv, all_zero, prim_root);

                _mm_storeu_si128(a[base..base + 4].as_mut_ptr() as *mut _, _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(c0, perm_mask)));
                _mm_storeu_si128(
                    a[base + offset..base + offset + 4].as_mut_ptr() as *mut _,
                    _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(c1, perm_mask)),
                );
                _mm_storeu_si128(
                    a[base + offset * 2..base + offset * 2 + 4].as_mut_ptr() as *mut _,
                    _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(c2, perm_mask)),
                );
                _mm_storeu_si128(
                    a[base + offset * 3..base + offset * 3 + 4].as_mut_ptr() as *mut _,
                    _mm256_castsi256_si128(_mm256_permutevar8x32_epi32(c3, perm_mask)),
                );
            }
        }
    }
}

#[allow(dead_code)]
#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn cooley_tukey_radix_4_butterfly_montgomery_modint_avx2(deg: usize, log: usize, a: &mut [Mint], cache: &FftCache<Mint>) {
    let twiddle = cache.twiddle_factors();
    for i in (0..log).step_by(2) {
        if i + 1 == log {
            let width = 1 << (i + 1);
            radix_2_kernel_cooley_tukey_avx2(deg, width, a, twiddle);
        } else {
            let width = 1 << (i + 2);
            radix_4_kernel_cooley_tukey_avx2(deg, width, a, cache, twiddle, super::common::radix_4_inner_montgomery_modint);
        }
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn cooley_tukey_radix_4_butterfly_inv_montgomery_modint_avx2(deg: usize, log: usize, a: &mut [Mint], cache: &FftCache<Mint>) {
    let twiddle = cache.twiddle_factors_inv();
    for i in (0..log).step_by(2) {
        if i + 1 == log {
            let width = 1 << (i + 1);
            radix_2_kernel_cooley_tukey_avx2(deg, width, a, twiddle);
        } else {
            let width = 1 << (i + 2);
            radix_4_kernel_cooley_tukey_avx2(deg, width, a, cache, twiddle, super::common::radix_4_inv_inner_montgomery_modint);
        }
    }
}

#[cfg(test)]
mod tests_gentleman_sande {
    use super::super::common::bit_reverse;
    use super::super::FftCache;
    use super::{gentleman_sande_radix_4_butterfly_inv_montgomery_modint_avx2, gentleman_sande_radix_4_butterfly_montgomery_modint_avx2};
    use modint::{Mod998244353, MontgomeryModint};

    type MontMint998244353 = MontgomeryModint<Mod998244353<u32>, u32>;

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

    const N: u32 = 1 << 7;

    #[test]
    fn gentleman_sande_radix_4_montgomery_modint_test() {
        let data: Vec<MontMint998244353> = (1..=N).map(|v| MontMint998244353::new(v)).collect();
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

    type MontMint998244353 = MontgomeryModint<Mod998244353<u32>, u32>;

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

    const N: u32 = 1 << 8;

    #[test]
    fn cooley_tukey_radix_8_montgomery_modint_test() {
        let data: Vec<MontMint998244353> = (1..=N).map(|v| MontMint998244353::new(v)).collect();
        let mut data1 = data.clone();
        fft_cooley_tukey_radix_4_montgomery_modint_avx2(&mut data1);
        ifft_cooley_tukey_radix_4_montgomery_modint_avx2(&mut data1);
        assert_eq!(data, data1);
    }
}
