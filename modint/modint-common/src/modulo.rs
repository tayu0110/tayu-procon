use std::{
    arch::x86_64::{
        __m256i, _mm256_add_epi32,  _mm256_and_si256, _mm256_blend_epi32, _mm256_cmpeq_epi32, _mm256_cmpgt_epi32, _mm256_max_epu32, _mm256_min_epu32, _mm256_mul_epu32,
        _mm256_mullo_epi32, _mm256_setzero_si256, _mm256_shuffle_epi32, _mm256_sub_epi32, _mm256_xor_si256, _mm256_or_si256, _mm256_add_epi64
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
    fn restoration(t: u32) -> u32 {
        if t >= Self::N {
            t - Self::N
        } else {
            t
        }
    }

    // Vectorized Modulo Constants
    const NX8: __m256i = const_simd_register!(Self::N);
    const N2X8: __m256i = const_simd_register!(Self::N << 1);
    const N_PRIMEX8: __m256i = const_simd_register!(Self::N_PRIME);
    const RX8: __m256i = const_simd_register!(Self::R);
    const R2X8: __m256i = const_simd_register!(Self::R2);
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_addition_u32x8(a: __m256i, b: __m256i) -> __m256i {
        let res = _mm256_add_epi32(a, b);
        let mask = _mm256_cmpeq_epi32(res, _mm256_max_epu32(res, Self::N2X8));
        _mm256_sub_epi32(res, _mm256_and_si256(Self::N2X8, mask))
    }
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_subtraction_u32x8(a: __m256i, b: __m256i) -> __m256i {
        let mask = _mm256_cmpgt_epi32(b, a);
        _mm256_add_epi32(_mm256_sub_epi32(a, b), _mm256_and_si256(Self::N2X8, mask))
    }
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_reduction_u32x8(t: __m256i) -> __m256i {
        let t_np = _mm256_mullo_epi32(t, Self::N_PRIMEX8);
        let res_lo = _mm256_add_epi64(_mm256_mul_epu32(t_np, Self::NX8), _mm256_blend_epi32(t, _mm256_setzero_si256(), 0b10101010));
        let res_hi = _mm256_add_epi64(_mm256_mul_epu32(_mm256_shuffle_epi32(t_np, 0b10_11_00_01), Self::NX8), _mm256_blend_epi32(_mm256_shuffle_epi32(t, 0b10_11_00_01), _mm256_setzero_si256(), 0b10101010));
        _mm256_blend_epi32(_mm256_shuffle_epi32(res_lo, 0b10_11_00_01), res_hi, 0b10101010)
    }
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn montgomery_multiplication_u32x8(a: __m256i, b: __m256i) -> __m256i {
        let t_lo = _mm256_mul_epu32(a, b);
        let t_hi = _mm256_mul_epu32(_mm256_shuffle_epi32(a, 0b10_11_00_01), _mm256_shuffle_epi32(b, 0b10_11_00_01));
        let t_np = _mm256_mullo_epi32(_mm256_blend_epi32(t_lo, _mm256_shuffle_epi32(t_hi, 0b10_11_00_01), 0b10101010), Self::N_PRIMEX8);
        let n64x4 = _mm256_blend_epi32(Self::NX8, _mm256_setzero_si256(), 0b10101010);
        let res_lo = _mm256_add_epi64(t_lo, _mm256_mul_epu32(t_np, n64x4));
        let res_hi = _mm256_add_epi64(t_hi, _mm256_mul_epu32(_mm256_shuffle_epi32(t_np, 0b10_11_00_01), n64x4));
        _mm256_blend_epi32(_mm256_shuffle_epi32(res_lo, 0b10_11_00_01), res_hi, 0b10101010)
    }
    #[inline]
    #[target_feature(enable = "avx2")]
    unsafe fn restoration_u32x8(t: __m256i) -> __m256i {
        let mask = _mm256_or_si256(_mm256_cmpgt_epi32(t, Self::NX8), _mm256_cmpeq_epi32(t, Self::NX8));
        _mm256_sub_epi32(t, _mm256_and_si256(mask, Self::NX8))
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
        if fa || !fs { u } else { t }
    }
    #[inline]
    fn montgomery_subtraction(a: u32, b: u32) -> u32 {
        let (val, f) = a.overflowing_sub(b);
        if f { val.wrapping_add(Self::N) } else { val }
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
    fn montgomery_addition_u32x8(a: __m256i, b: __m256i) -> __m256i {
        let diff = unsafe { _mm256_sub_epi32(Self::NX8, a) };
        let mask = unsafe { _mm256_cmpeq_epi32(diff, _mm256_max_epu32(diff, b)) };
        let val = unsafe { _mm256_add_epi32(_mm256_sub_epi32(a, Self::NX8), b) };
        unsafe { _mm256_add_epi32(val, _mm256_and_si256(mask, Self::NX8)) }
    }
    #[inline]
    fn montgomery_subtraction_u32x8(a: __m256i, b: __m256i) -> __m256i {
        let mask = unsafe { _mm256_cmpeq_epi32(b, _mm256_max_epu32(a, b)) };
        let c_neg = unsafe { _mm256_sub_epi32(a, b) };
        unsafe { _mm256_add_epi32(c_neg, _mm256_and_si256(Self::NX8, mask)) }
    }
    #[inline]
    fn montgomery_reduction_u32x8(t: __m256i) -> __m256i {
        let t_ninv = unsafe { _mm256_mullo_epi32(t, Self::N_INVX8) };
        let t_ninv_n_lo = unsafe { _mm256_mul_epu32(t_ninv, Self::NX8) };
        let t_ninv_n_hi = unsafe { _mm256_mul_epu32(_mm256_shuffle_epi32(t_ninv, 0b10_11_00_01), Self::NX8) };
        let mr = unsafe { _mm256_blend_epi32(_mm256_shuffle_epi32(t_ninv_n_lo, 0b10_11_00_01), t_ninv_n_hi, 0b10101010) };
        let zero = unsafe { _mm256_setzero_si256() };
        let mask = unsafe { _mm256_cmpeq_epi32(mr, zero) };
        let mask = unsafe { _mm256_and_si256(Self::NX8, _mm256_xor_si256(mask, _mm256_cmpeq_epi32(mask, mask))) };
        unsafe { _mm256_sub_epi32(mask, mr) }
    }
    #[inline]
    fn montgomery_multiplication_u32x8(a: __m256i, b: __m256i) -> __m256i {
        let t1 = unsafe { _mm256_mul_epu32(a, b) };
        let t2 = unsafe { _mm256_mul_epu32(_mm256_shuffle_epi32(a, 0b10_11_00_01), _mm256_shuffle_epi32(b, 0b10_11_00_01)) };
        let t_modinv = unsafe { _mm256_mullo_epi32(_mm256_blend_epi32(t1, _mm256_shuffle_epi32(t2, 0b10_11_00_01), 0b10101010), Self::N_INVX8) };
        let c = unsafe {
            _mm256_blend_epi32(
                _mm256_shuffle_epi32(_mm256_mul_epu32(t_modinv, Self::NX8), 0b10_11_00_01),
                _mm256_mul_epu32(_mm256_shuffle_epi32(t_modinv, 0b10_11_00_01), Self::NX8),
                0b10101010,
            )
        };
        let t = unsafe { _mm256_blend_epi32(_mm256_shuffle_epi32(t1, 0b10_11_00_01), t2, 0b10101010) };
        let one = unsafe { _mm256_cmpeq_epi32(c, c) };
        let mask = unsafe { _mm256_and_si256(Self::NX8, _mm256_xor_si256(one, _mm256_cmpeq_epi32(_mm256_min_epu32(t, c), c))) };
        unsafe { _mm256_add_epi32(mask, _mm256_sub_epi32(t, c)) }
    }
    #[inline]
    fn restoration_u32x8(t: __m256i) -> __m256i { t }
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

macro_rules! impl_lazy_modulo {
    ( $({ $name:ident, $modulo:literal, $prim_root:literal },)* ) => {
        $(
            #[derive(Debug, Clone, marker::Copy, PartialEq, Eq)]
            pub enum $name {}
            impl LazyMontgomeryModulo for $name {
                const N: u32 = $modulo;
            }
            impl Modulo for $name {
                const MOD: u32 = <Self as LazyMontgomeryModulo>::N;
                const R: u32 = <Self as LazyMontgomeryModulo>::R;
                const R2: u32 = <Self as LazyMontgomeryModulo>::R2;
                const PRIM_ROOT: u32 = $prim_root;
                const MODX8: __m256i = <Self as LazyMontgomeryModulo>::NX8;
                const RX8: __m256i = <Self as LazyMontgomeryModulo>::RX8;
                const R2X8: __m256i = <Self as LazyMontgomeryModulo>::R2X8;
                #[inline(always)] fn add(a: u32, b: u32) -> u32 { <Self as LazyMontgomeryModulo>::montgomery_addition(a, b) }
                #[inline(always)] fn subtract(a: u32, b: u32) -> u32 { <Self as LazyMontgomeryModulo>::montgomery_subtraction(a, b) }
                #[inline(always)] fn multiply(a: u32, b: u32) -> u32 { <Self as LazyMontgomeryModulo>::montgomery_multiplication(a, b) }
                #[inline(always)] fn reduce(t: u32) -> u32 { <Self as LazyMontgomeryModulo>::montgomery_reduction(t) }
                #[inline(always)] fn restore(t: u32) -> u32 { <Self as LazyMontgomeryModulo>::restoration(t) }
                #[inline(always)] fn addx8(a: __m256i, b: __m256i) -> __m256i { unsafe { <Self as LazyMontgomeryModulo>::montgomery_addition_u32x8(a, b) } }
                #[inline(always)] fn subtractx8(a: __m256i, b: __m256i) -> __m256i { unsafe { <Self as LazyMontgomeryModulo>::montgomery_subtraction_u32x8(a, b) } }
                #[inline(always)] fn multiplyx8(a: __m256i, b: __m256i) -> __m256i { unsafe { <Self as LazyMontgomeryModulo>::montgomery_multiplication_u32x8(a, b) } }
                #[inline(always)] fn reducex8(t: __m256i) -> __m256i { unsafe { <Self as LazyMontgomeryModulo>::montgomery_reduction_u32x8(t) } }
                #[inline(always)] fn restorex8(t: __m256i) -> __m256i { unsafe { <Self as LazyMontgomeryModulo>::restoration_u32x8(t) } }
            }
        )*
    };
}

// https://www.mathenachia.blog/ntt-mod-list-01/
impl_lazy_modulo!(
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

macro_rules! impl_large_modulo {
    ( $({ $name:ident, $modulo:literal, $prim_root:literal },)* ) => {
        $(
            #[derive(Debug, Clone, marker::Copy, PartialEq, Eq)]
            pub enum $name {}
            impl LargeMontgomeryModulo for $name {
                const N: u32 = $modulo;
            }
            impl Modulo for $name {
                const MOD: u32 = <Self as LargeMontgomeryModulo>::N;
                const R: u32 = <Self as LargeMontgomeryModulo>::R;
                const R2: u32 = <Self as LargeMontgomeryModulo>::R2;
                const PRIM_ROOT: u32 = $prim_root;
                const MODX8: __m256i = <Self as LargeMontgomeryModulo>::NX8;
                const RX8: __m256i = <Self as LargeMontgomeryModulo>::RX8;
                const R2X8: __m256i = <Self as LargeMontgomeryModulo>::R2X8;
                #[inline(always)] fn add(a: u32, b: u32) -> u32 { <Self as LargeMontgomeryModulo>::montgomery_addition(a, b) }
                #[inline(always)] fn subtract(a: u32, b: u32) -> u32 { <Self as LargeMontgomeryModulo>::montgomery_subtraction(a, b) }
                #[inline(always)] fn multiply(a: u32, b: u32) -> u32 { <Self as LargeMontgomeryModulo>::montgomery_multiplication(a, b) }
                #[inline(always)] fn reduce(t: u32) -> u32 { <Self as LargeMontgomeryModulo>::montgomery_reduction(t) }
                #[inline(always)] fn restore(t: u32) -> u32 { <Self as LargeMontgomeryModulo>::restoration(t) }
                #[inline(always)] fn addx8(a: __m256i, b: __m256i) -> __m256i { <Self as LargeMontgomeryModulo>::montgomery_addition_u32x8(a, b) }
                #[inline(always)] fn subtractx8(a: __m256i, b: __m256i) -> __m256i { <Self as LargeMontgomeryModulo>::montgomery_subtraction_u32x8(a, b) }
                #[inline(always)] fn multiplyx8(a: __m256i, b: __m256i) -> __m256i { <Self as LargeMontgomeryModulo>::montgomery_multiplication_u32x8(a, b) }
                #[inline(always)] fn reducex8(t: __m256i) -> __m256i { <Self as LargeMontgomeryModulo>::montgomery_reduction_u32x8(t) }
                #[inline(always)] fn restorex8(t: __m256i) -> __m256i { <Self as LargeMontgomeryModulo>::restoration_u32x8(t) }
            }
        )*        
    };
}

impl_large_modulo!(
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
