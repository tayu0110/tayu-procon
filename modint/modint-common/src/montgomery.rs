use super::modulo::Modulo;
use std::arch::x86_64::{
    __m256i, _mm256_add_epi32 as addi32, _mm256_add_epi64 as addi64, _mm256_and_si256 as and256, _mm256_blend_epi32 as blendi32, _mm256_cmpeq_epi32 as eqi32, _mm256_cmpgt_epi32,
    _mm256_max_epu32 as maxu32, _mm256_min_epu32, _mm256_mul_epu32 as mulu32, _mm256_mullo_epi32 as mulloi32, _mm256_or_si256, _mm256_setzero_si256 as zero256, _mm256_shuffle_epi32 as shufi32,
    _mm256_sub_epi32 as subi32, _mm256_xor_si256 as xor256,
};

// Montgomery Operators
// These functions support "Lazy Reduction" if the Modulo::N <= THRESHOLD.
// In case that normalization does not performed, Montgomery Reduction receives a value T sutisfying 0 <= T < NR as an argument, and return a value MR(T) satisfying 0 <= MR(T) < 2N.
// As above, the range of the argument for Montgomery Reduction includes the range of a return value.
// So, the normalization can be delayed until the normalized value will be needed.
const THRESHOLD: u32 = 1 << 30;

#[inline]
pub const fn mreduce<M: Modulo>(t: u32) -> u32 {
    if M::N > THRESHOLD {
        let (t, f) = (((t.wrapping_mul(M::N_INV) as u64).wrapping_mul(M::N as u64) >> 32) as u32).overflowing_neg();
        t.wrapping_add(M::N & (f as u32).wrapping_neg())
    } else {
        ((t as u64 + t.wrapping_mul(M::N_PRIME) as u64 * M::N as u64) >> 32) as u32
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn mreducex8<M: Modulo>(t: __m256i) -> __m256i {
    if M::N > THRESHOLD {
        let t_ninv = mulloi32(t, M::N_INVX8);
        let t_ninv_n_lo = mulu32(t_ninv, M::NX8);
        let t_ninv_n_hi = mulu32(shufi32(t_ninv, 0b10_11_00_01), M::NX8);
        let mr = blendi32(shufi32(t_ninv_n_lo, 0b10_11_00_01), t_ninv_n_hi, 0b10101010);
        let zero = zero256();
        let mask = eqi32(mr, zero);
        let mask = and256(M::NX8, xor256(mask, eqi32(mask, mask)));
        subi32(mask, mr)
    } else {
        let t_np = mulloi32(t, M::N_PRIMEX8);
        let res_lo = addi64(mulu32(t_np, M::NX8), blendi32(t, zero256(), 0b10101010));
        let res_hi = addi64(mulu32(shufi32(t_np, 0b10_11_00_01), M::NX8), blendi32(shufi32(t, 0b10_11_00_01), zero256(), 0b10101010));
        blendi32(shufi32(res_lo, 0b10_11_00_01), res_hi, 0b10101010)
    }
}

#[inline]
pub const fn mmul<M: Modulo>(a: u32, b: u32) -> u32 {
    let t = a as u64 * b as u64;
    if M::N > THRESHOLD {
        let (t, f) = ((t >> 32) as u32).overflowing_sub((((t as u32).wrapping_mul(M::N_INV) as u64).wrapping_mul(M::N as u64) >> 32) as u32);
        t.wrapping_add(M::N & (f as u32).wrapping_neg())
    } else {
        ((t + (t as u32).wrapping_mul(M::N_PRIME) as u64 * M::N as u64) >> 32) as u32
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn mmulx8<M: Modulo>(a: __m256i, b: __m256i) -> __m256i {
    if M::N > THRESHOLD {
        let t1 = mulu32(a, b);
        let t2 = mulu32(shufi32(a, 0b10_11_00_01), shufi32(b, 0b10_11_00_01));
        let t_modinv = mulloi32(blendi32(t1, shufi32(t2, 0b10_11_00_01), 0b10101010), M::N_INVX8);
        let c = blendi32(shufi32(mulu32(t_modinv, M::NX8), 0b10_11_00_01), mulu32(shufi32(t_modinv, 0b10_11_00_01), M::NX8), 0b10101010);
        let t = blendi32(shufi32(t1, 0b10_11_00_01), t2, 0b10101010);
        let one = eqi32(c, c);
        let mask = and256(M::NX8, xor256(one, eqi32(_mm256_min_epu32(t, c), c)));
        addi32(mask, subi32(t, c))
    } else {
        let t_lo = mulu32(a, b);
        let t_hi = mulu32(shufi32(a, 0b10_11_00_01), shufi32(b, 0b10_11_00_01));
        let t_np = mulloi32(blendi32(t_lo, shufi32(t_hi, 0b10_11_00_01), 0b10101010), M::N_PRIMEX8);
        let n64x4 = blendi32(M::NX8, zero256(), 0b10101010);
        let res_lo = addi64(t_lo, mulu32(t_np, n64x4));
        let res_hi = addi64(t_hi, mulu32(shufi32(t_np, 0b10_11_00_01), n64x4));
        blendi32(shufi32(res_lo, 0b10_11_00_01), res_hi, 0b10101010)
    }
}

#[inline]
pub const fn mrestore<M: Modulo>(t: u32) -> u32 { t - if M::N <= THRESHOLD { M::N & ((t >= M::N) as u32).wrapping_neg() } else { 0 } }

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn mrestorex8<M: Modulo>(t: __m256i) -> __m256i {
    if M::N > THRESHOLD {
        t
    } else {
        let mask = _mm256_or_si256(_mm256_cmpgt_epi32(t, M::NX8), eqi32(t, M::NX8));
        subi32(t, and256(mask, M::NX8))
    }
}

#[inline]
pub const fn madd<M: Modulo>(a: u32, b: u32) -> u32 {
    if M::N > THRESHOLD {
        let (t, fa) = a.overflowing_add(b);
        let (u, fs) = t.overflowing_sub(M::N);
        let f = (fa || !fs) as u32;
        f * u + (1 - f) * t
    } else {
        let res = a + b;
        res - (((res >= M::N2) as u32).wrapping_neg() & M::N2)
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn maddx8<M: Modulo>(a: __m256i, b: __m256i) -> __m256i {
    if M::N > THRESHOLD {
        let diff = subi32(M::NX8, a);
        let mask = eqi32(diff, maxu32(diff, b));
        let val = addi32(subi32(a, M::NX8), b);
        addi32(val, and256(mask, M::NX8))
    } else {
        let res = addi32(a, b);
        let mask = eqi32(res, maxu32(res, M::N2X8));
        subi32(res, and256(M::N2X8, mask))
    }
}

#[inline]
pub const fn msub<M: Modulo>(a: u32, b: u32) -> u32 {
    let (res, f) = a.overflowing_sub(b);
    if M::N > THRESHOLD {
        res.wrapping_add(M::N & (f as u32).wrapping_neg())
    } else {
        res.wrapping_add(M::N2 & (f as u32).wrapping_neg())
    }
}

#[inline]
#[target_feature(enable = "avx2")]
pub unsafe fn msubx8<M: Modulo>(a: __m256i, b: __m256i) -> __m256i {
    if M::N > THRESHOLD {
        let mask = eqi32(b, maxu32(a, b));
        let c_neg = subi32(a, b);
        addi32(c_neg, and256(M::NX8, mask))
    } else {
        let mask = _mm256_cmpgt_epi32(b, a);
        addi32(subi32(a, b), and256(M::N2X8, mask))
    }
}
