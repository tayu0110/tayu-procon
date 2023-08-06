use std::{
    arch::x86_64::{
        __m256i, _mm256_add_epi32 as addi32, _mm256_add_epi64 as addi64, _mm256_and_si256 as and256, _mm256_blend_epi32 as blendi32, _mm256_cmpeq_epi32 as eqi32, _mm256_cmpgt_epi32,
        _mm256_max_epu32 as maxu32, _mm256_min_epu32, _mm256_mul_epu32 as mulu32, _mm256_mullo_epi32 as mulloi32, _mm256_or_si256, _mm256_setzero_si256 as zero256, _mm256_shuffle_epi32 as shufi32,
        _mm256_sub_epi32 as subi32, _mm256_xor_si256 as xor256,
    },
    fmt::Debug,
    marker,
};

union ConstSimdTrick {
    arr: [u32; 8],
    reg: __m256i,
}

macro_rules! const_simd_register {
    ( $v:expr ) => { unsafe { ConstSimdTrick { arr: [$v; 8] }.reg } };
}

macro_rules! newtons_method {
    ( $mod:expr ) => {{
            let inv = $mod.wrapping_mul(2u32.wrapping_sub($mod.wrapping_mul($mod)));
            let inv = inv.wrapping_mul(2u32.wrapping_sub($mod.wrapping_mul(inv)));
            let inv = inv.wrapping_mul(2u32.wrapping_sub($mod.wrapping_mul(inv)));
            let inv = inv.wrapping_mul(2u32.wrapping_sub($mod.wrapping_mul(inv)));
            inv.wrapping_mul(2u32.wrapping_sub($mod.wrapping_mul(inv)))
    }};
}

// This trait expresses "Lazy Reduction".
// In case that normalization does not performed, Montgomery Reduction receives a value T sutisfying 0 <= T < NR as an argument, and return a value MR(T) satisfying 0 <= MR(T) < 2N.
// As above, the range of the argument for Montgomery Reduction includes the range of a return value.
// So, the normalization can be delayed until the normalized value will be needed.
pub trait LazyMontgomeryModulo: Clone + marker::Copy + PartialEq + Eq + Debug {
    const N: u32;
    const N2: u32 = Self::N << 1;
    // NN' = -1 mod R
    const N_PRIME: u32 = newtons_method!(Self::N).wrapping_neg();
    // R = 2^32 mod N
    const R: u32 = ((1u64 << 32) % Self::N as u64) as u32;
    // R^2 = 2^64 mod N
    const R2: u32 = ((Self::N as u64).wrapping_neg() % Self::N as u64) as u32;
    #[inline]
    fn montgomery_addition(a: u32, b: u32) -> u32 {
        let res = a + b;
        res - (((res >= Self::N2) as u32).wrapping_neg() & Self::N2)
    }
    #[inline]
    fn montgomery_subtraction(a: u32, b: u32) -> u32 {
        let (res, f) = a.overflowing_sub(b);
        res.wrapping_add(Self::N2 & (f as u32).wrapping_neg())
    }
    // t <- MR(T) = (T + (TN' mod R)*N)/R
    //  if t >= N then return t - N else return t
    //      0 <= T < NR
    //      NN' = -1 (mod R)
    #[inline]
    fn montgomery_reduction(t: u32) -> u32 { ((t as u64 + t.wrapping_mul(Self::N_PRIME) as u64 * Self::N as u64) >> 32) as u32 }
    #[inline]
    fn montgomery_multiplication(a: u32, b: u32) -> u32 {
        let t = a as u64 * b as u64;
        ((t + (t as u32).wrapping_mul(Self::N_PRIME) as u64 * Self::N as u64) >> 32) as u32
    }
    #[inline]
    fn restoration(t: u32) -> u32 { t - (Self::N & ((t >= Self::N) as u32).wrapping_neg()) }

    // Vectorized Modulo Constants
    const NX8: __m256i = const_simd_register!(Self::N);
    const N2X8: __m256i = const_simd_register!(Self::N << 1);
    const N_PRIMEX8: __m256i = const_simd_register!(Self::N_PRIME);
    const RX8: __m256i = const_simd_register!(Self::R);
    const R2X8: __m256i = const_simd_register!(Self::R2);
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_addition_u32x8(a: __m256i, b: __m256i) -> __m256i {
        let res = addi32(a, b);
        let mask = eqi32(res, maxu32(res, Self::N2X8));
        subi32(res, and256(Self::N2X8, mask))
    }
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_subtraction_u32x8(a: __m256i, b: __m256i) -> __m256i {
        let mask = _mm256_cmpgt_epi32(b, a);
        addi32(subi32(a, b), and256(Self::N2X8, mask))
    }
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_reduction_u32x8(t: __m256i) -> __m256i {
        let t_np = mulloi32(t, Self::N_PRIMEX8);
        let res_lo = addi64(mulu32(t_np, Self::NX8), blendi32(t, zero256(), 0b10101010));
        let res_hi = addi64(mulu32(shufi32(t_np, 0b10_11_00_01), Self::NX8), blendi32(shufi32(t, 0b10_11_00_01), zero256(), 0b10101010));
        blendi32(shufi32(res_lo, 0b10_11_00_01), res_hi, 0b10101010)
    }
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_multiplication_u32x8(a: __m256i, b: __m256i) -> __m256i {
        let t_lo = mulu32(a, b);
        let t_hi = mulu32(shufi32(a, 0b10_11_00_01), shufi32(b, 0b10_11_00_01));
        let t_np = mulloi32(blendi32(t_lo, shufi32(t_hi, 0b10_11_00_01), 0b10101010), Self::N_PRIMEX8);
        let n64x4 = blendi32(Self::NX8, zero256(), 0b10101010);
        let res_lo = addi64(t_lo, mulu32(t_np, n64x4));
        let res_hi = addi64(t_hi, mulu32(shufi32(t_np, 0b10_11_00_01), n64x4));
        blendi32(shufi32(res_lo, 0b10_11_00_01), res_hi, 0b10101010)
    }
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn restoration_u32x8(t: __m256i) -> __m256i {
        let mask = _mm256_or_si256(_mm256_cmpgt_epi32(t, Self::NX8), eqi32(t, Self::NX8));
        subi32(t, and256(mask, Self::NX8))
    }
}

pub trait LargeMontgomeryModulo: Clone + marker::Copy + PartialEq + Eq + Debug {
    const N: u32;
    // N * N_INV = 1 mod R
    const N_INV: u32 = newtons_method!(Self::N);
    // R = 2^32 mod N
    const R: u32 = ((1u64 << 32) % Self::N as u64) as u32;
    // R2 = 2^64 mod N
    const R2: u32 = ((Self::N as u64).wrapping_neg() % Self::N as u64) as u32;
    #[inline]
    fn montgomery_addition(a: u32, b: u32) -> u32 {
        let (t, fa) = a.overflowing_add(b);
        let (u, fs) = t.overflowing_sub(Self::N);
        if fa || !fs {
            u
        } else {
            t
        }
    }
    #[inline]
    fn montgomery_subtraction(a: u32, b: u32) -> u32 {
        let (val, f) = a.overflowing_sub(b);
        if f {
            val.wrapping_add(Self::N)
        } else {
            val
        }
    }
    // t <- MR(T) = floor(T/R) - floor((TN' mod R)*N/R)
    //  if t < 0 then return t + N else return t
    //      T := a (0 <= T < NR)
    //      N := MOD
    //      N':= MOD_INV    NN' = 1 (mod R)
    //      R := R
    #[inline]
    fn montgomery_reduction(t: u32) -> u32 {
        let (t, f) = (((t.wrapping_mul(Self::N_INV) as u64).wrapping_mul(Self::N as u64) >> 32) as u32).overflowing_neg();
        t.wrapping_add(Self::N & (f as u32).wrapping_neg())
    }
    #[inline]
    fn montgomery_multiplication(a: u32, b: u32) -> u32 {
        let t = a as u64 * b as u64;
        let (t, f) = ((t >> 32) as u32).overflowing_sub((((t as u32).wrapping_mul(Self::N_INV) as u64).wrapping_mul(Self::N as u64) >> 32) as u32);
        t.wrapping_add(Self::N & (f as u32).wrapping_neg())
    }
    #[inline(always)]
    fn restoration(t: u32) -> u32 { t }

    // Vectorized Modulo Constants
    const NX8: __m256i = const_simd_register!(Self::N);
    const N_INVX8: __m256i = const_simd_register!(Self::N_INV);
    const RX8: __m256i = const_simd_register!(Self::R);
    const R2X8: __m256i = const_simd_register!(Self::R2);
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_addition_u32x8(a: __m256i, b: __m256i) -> __m256i {
        let diff = subi32(Self::NX8, a);
        let mask = eqi32(diff, maxu32(diff, b));
        let val = addi32(subi32(a, Self::NX8), b);
        addi32(val, and256(mask, Self::NX8))
    }
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_subtraction_u32x8(a: __m256i, b: __m256i) -> __m256i {
        let mask = eqi32(b, maxu32(a, b));
        let c_neg = subi32(a, b);
        addi32(c_neg, and256(Self::NX8, mask))
    }
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_reduction_u32x8(t: __m256i) -> __m256i {
        let t_ninv = mulloi32(t, Self::N_INVX8);
        let t_ninv_n_lo = mulu32(t_ninv, Self::NX8);
        let t_ninv_n_hi = mulu32(shufi32(t_ninv, 0b10_11_00_01), Self::NX8);
        let mr = blendi32(shufi32(t_ninv_n_lo, 0b10_11_00_01), t_ninv_n_hi, 0b10101010);
        let zero = zero256();
        let mask = eqi32(mr, zero);
        let mask = and256(Self::NX8, xor256(mask, eqi32(mask, mask)));
        subi32(mask, mr)
    }
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_multiplication_u32x8(a: __m256i, b: __m256i) -> __m256i {
        let t1 = mulu32(a, b);
        let t2 = mulu32(shufi32(a, 0b10_11_00_01), shufi32(b, 0b10_11_00_01));
        let t_modinv = mulloi32(blendi32(t1, shufi32(t2, 0b10_11_00_01), 0b10101010), Self::N_INVX8);
        let c = blendi32(shufi32(mulu32(t_modinv, Self::NX8), 0b10_11_00_01), mulu32(shufi32(t_modinv, 0b10_11_00_01), Self::NX8), 0b10101010);
        let t = blendi32(shufi32(t1, 0b10_11_00_01), t2, 0b10101010);
        let one = eqi32(c, c);
        let mask = and256(Self::NX8, xor256(one, eqi32(_mm256_min_epu32(t, c), c)));
        addi32(mask, subi32(t, c))
    }
    #[inline]
    unsafe fn restoration_u32x8(t: __m256i) -> __m256i { t }
}

pub trait Modulo: Clone + marker::Copy + PartialEq + Eq + Debug {
    const MOD: u32;
    const R: u32;
    const R2: u32;
    const PRIM_ROOT: u32;
    const MODX8: __m256i;
    const RX8: __m256i;
    const R2X8: __m256i;
    fn add(a: u32, b: u32) -> u32;
    fn subtract(a: u32, b: u32) -> u32;
    fn multiply(a: u32, b: u32) -> u32;
    fn reduce(t: u32) -> u32;
    fn restore(t: u32) -> u32;
    fn addx8(a: __m256i, b: __m256i) -> __m256i;
    fn subtractx8(a: __m256i, b: __m256i) -> __m256i;
    fn multiplyx8(a: __m256i, b: __m256i) -> __m256i;
    fn reducex8(t: __m256i) -> __m256i;
    fn restorex8(t: __m256i) -> __m256i;
}

use LargeMontgomeryModulo as LgModulo;
use LazyMontgomeryModulo as LzModulo;

macro_rules! impl_modulo {
    ( $trait:ident, $({ $name:ident, $modulo:literal, $prim_root:literal },)* ) => {
        $(
            #[derive(Debug, Clone, marker::Copy, PartialEq, Eq)]
            pub enum $name {}
            impl $trait for $name {
                const N: u32 = $modulo;
            }
            impl Modulo for $name {
                const MOD: u32 = <Self as $trait>::N;
                const R: u32 = <Self as $trait>::R;
                const R2: u32 = <Self as $trait>::R2;
                const PRIM_ROOT: u32 = $prim_root;
                const MODX8: __m256i = <Self as $trait>::NX8;
                const RX8: __m256i = <Self as $trait>::RX8;
                const R2X8: __m256i = <Self as $trait>::R2X8;
                #[inline(always)] fn add(a: u32, b: u32) -> u32 { <Self as $trait>::montgomery_addition(a, b) }
                #[inline(always)] fn subtract(a: u32, b: u32) -> u32 { <Self as $trait>::montgomery_subtraction(a, b) }
                #[inline(always)] fn multiply(a: u32, b: u32) -> u32 { <Self as $trait>::montgomery_multiplication(a, b) }
                #[inline(always)] fn reduce(t: u32) -> u32 { <Self as $trait>::montgomery_reduction(t) }
                #[inline(always)] fn restore(t: u32) -> u32 { <Self as $trait>::restoration(t) }
                #[inline(always)] fn addx8(a: __m256i, b: __m256i) -> __m256i { unsafe { <Self as $trait>::montgomery_addition_u32x8(a, b) } }
                #[inline(always)] fn subtractx8(a: __m256i, b: __m256i) -> __m256i { unsafe { <Self as $trait>::montgomery_subtraction_u32x8(a, b) } }
                #[inline(always)] fn multiplyx8(a: __m256i, b: __m256i) -> __m256i { unsafe { <Self as $trait>::montgomery_multiplication_u32x8(a, b) } }
                #[inline(always)] fn reducex8(t: __m256i) -> __m256i { unsafe { <Self as $trait>::montgomery_reduction_u32x8(t) } }
                #[inline(always)] fn restorex8(t: __m256i) -> __m256i { unsafe { <Self as $trait>::restoration_u32x8(t) } }
            }
        )*
    };
}

// https://www.mathenachia.blog/ntt-mod-list-01/
impl_modulo!(
    LzModulo,
    { Mod167772161, 167772161, 3 },
    { Mod377487361, 377487361, 7 },
    { Mod469762049, 469762049, 3 },
    { Mod595591169, 595591169, 3 },
    { Mod645922817, 645922817, 3 },
    { Mod754974721, 754974721, 11 },
    { Mod880803841, 880803841, 26 },
    { Mod897581057, 897581057, 3 },
    { Mod998244353, 998244353, 3 },
    { Mod1000000007, 1000000007, 5 },
);

impl_modulo!(
    LgModulo,
    { Mod1107296257, 1107296257, 10	},
    { Mod1224736769, 1224736769, 3 },
    { Mod1300234241, 1300234241, 3 },
    { Mod1484783617, 1484783617, 5 },
    { Mod1711276033, 1711276033, 29	},
    { Mod1811939329, 1811939329, 13	},
    { Mod2013265921, 2013265921, 31	},
    { Mod2088763393, 2088763393, 5 },
    { Mod2113929217, 2113929217, 5 },
    { Mod2130706433, 2130706433, 3 },
    { Mod2281701377, 2281701377, 3 },
    { Mod2483027969, 2483027969, 3 },
    { Mod2533359617, 2533359617, 3 },
    { Mod2634022913, 2634022913, 3 },
    { Mod2717908993, 2717908993, 5 },
    { Mod2868903937, 2868903937, 35 },
    { Mod2885681153, 2885681153, 3 },
    { Mod3221225473, 3221225473, 5 },
    { Mod3238002689, 3238002689, 3 },
    { Mod3489660929, 3489660929, 3 },
    { Mod3892314113, 3892314113, 3 },
    { Mod3942645761, 3942645761, 3 },
    { Mod4076863489, 4076863489, 7 },
    { Mod4194304001, 4194304001, 3 },
);
