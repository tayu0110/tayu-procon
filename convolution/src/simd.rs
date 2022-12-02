use super::FftCache;
use modint::{Mod998244353, Modulo, MontgomeryModint};
#[cfg(target_arch = "x86")]
use std::arch::x86::*;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{
    __m256i, _mm256_add_epi64, _mm256_blendv_epi8, _mm256_cmpgt_epi32, _mm256_mul_epu32, _mm256_mullo_epi32, _mm256_set1_epi32, _mm256_set_epi64x,
    _mm256_store_si256, _mm256_sub_epi32, _mm_add_epi32, _mm_and_si128, _mm_set1_epi32, _mm_set_epi32, _mm_store_si128,
};

type Mint = MontgomeryModint<Mod998244353<u32>, u32>;
type Radix4Inner<T> = fn(T, T, T, T, &FftCache<T>) -> (T, T, T, T);

#[repr(C, align(32))]
struct AlignedArrayu32x4 {
    val: [u32; 4],
}

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
    _mm256_blendv_epi8(c_neg, c, mask)
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn radix_4_kernel_gentleman_sande_avx2(
    deg: usize,
    width: usize,
    a: &mut [Mint],
    cache: &FftCache<Mint>,
    twiddle: &[Mint],
    radix4_inner: Radix4Inner<Mint>,
) {
    let log = width.trailing_zeros();

    let exp = deg >> log;
    let exp_base = _mm_set_epi32(exp as i32 * 3, exp as i32 * 2, exp as i32, 0);
    let exp_mask = _mm_set1_epi32(deg as i32 - 1);
    let mut exp_now = AlignedArrayu32x4 { val: [0u32; 4] };

    let montgomery_constant_modulo_inv = _mm256_set1_epi32(Mod998244353::<u32>::montgomery_constant_modulo_inv() as i32);
    let montgomery_constant_modulo = _mm256_set1_epi32(Mod998244353::<u32>::modulo() as i32);
    let all_zero = _mm256_set1_epi32(0);
    let mut dest = AlignedArrayu32x8 { val: [0u32; 8] };

    let offset = width >> 2;
    for top in (0..deg).step_by(width) {
        let (id0, id1, id2, id3) = (top, top + offset, top + offset * 2, top + offset * 3);
        let (c0, c1, c2, c3) = (a[id0], a[id1], a[id2], a[id3]);
        let (c0, c1, c2, c3) = radix4_inner(c0, c1, c2, c3, cache);
        a[id0] = c0;
        a[id2] = c1;
        a[id1] = c2;
        a[id3] = c3;
        let mut exp_cache = exp_base.clone();
        for base in top + 1..top + offset {
            let (id0, id1, id2, id3) = (base, base + offset, base + offset * 2, base + offset * 3);
            let (c0, c1, c2, c3) = (a[id0], a[id1], a[id2], a[id3]);
            let (c0, c1, c2, c3) = radix4_inner(c0, c1, c2, c3, cache);

            _mm_store_si128(exp_now.val.as_mut_ptr() as *mut _, exp_cache);

            let (w1, w2, w3) = (
                twiddle[exp_now.val[1] as usize],
                twiddle[exp_now.val[2] as usize],
                twiddle[exp_now.val[3] as usize],
            );

            let ws = _mm256_set_epi64x(
                w3.val_montgomery_expression() as i64,
                w2.val_montgomery_expression() as i64,
                w1.val_montgomery_expression() as i64,
                Mint::one().val_montgomery_expression() as i64,
            );
            let cs = _mm256_set_epi64x(
                c3.val_montgomery_expression() as i64,
                c2.val_montgomery_expression() as i64,
                c1.val_montgomery_expression() as i64,
                c0.val_montgomery_expression() as i64,
            );

            let res = montgomery_multiplication_u32x4(ws, cs, montgomery_constant_modulo, montgomery_constant_modulo_inv, all_zero);
            _mm256_store_si256(dest.val.as_mut_ptr() as *mut _, res);

            a[id0] = Mint::from_montgomery_expression(dest.val[1]);
            a[id2] = Mint::from_montgomery_expression(dest.val[3]);
            a[id1] = Mint::from_montgomery_expression(dest.val[5]);
            a[id3] = Mint::from_montgomery_expression(dest.val[7]);

            exp_cache = _mm_add_epi32(exp_cache, exp_base);
            exp_cache = _mm_and_si128(exp_cache, exp_mask);
        }
    }
}
