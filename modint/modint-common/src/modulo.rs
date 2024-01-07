#[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
use std::arch::x86_64::__m256i;
use std::fmt::Debug;
use std::marker;
use std::mem::transmute;

pub trait Modulo: Clone + marker::Copy + PartialEq + Eq + Debug {
    const N: u32;
    const N2: u32 = Self::N.wrapping_mul(2);
    // N * N_INV = 1 mod R
    const N_INV: u32 = {
        let mut inv = Self::N.wrapping_mul(2u32.wrapping_sub(Self::N.wrapping_mul(Self::N)));
        while Self::N.wrapping_mul(inv) != 1 {
            inv = inv.wrapping_mul(2u32.wrapping_sub(Self::N.wrapping_mul(inv)));
        }
        inv
    };
    // NN' = -1 mod R
    const N_PRIME: u32 = Self::N_INV.wrapping_neg();
    // R = 2^32 mod N
    const R: u32 = ((1u64 << 32) % Self::N as u64) as u32;
    // R2 = 2^64 mod N
    const R2: u32 = ((Self::N as u64).wrapping_neg() % Self::N as u64) as u32;
    const PRIM_ROOT: u32;
    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    const NX8: __m256i = unsafe { transmute([Self::N; 8]) };
    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    const N2X8: __m256i = unsafe { transmute([Self::N2; 8]) };
    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    const N_INVX8: __m256i = unsafe { transmute([Self::N_INV; 8]) };
    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    const N_PRIMEX8: __m256i = unsafe { transmute([Self::N_PRIME; 8]) };
    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    const RX8: __m256i = unsafe { transmute([Self::R; 8]) };
    #[cfg(any(target_arch = "x86_64", target_arch = "x86"))]
    const R2X8: __m256i = unsafe { transmute([Self::R2; 8]) };
}

macro_rules! impl_modulo {
    ( $({ $name:ident, $modulo:literal, $prim_root:literal },)* ) => {
        $(
            #[derive(Debug, Clone, marker::Copy, PartialEq, Eq)]
            pub enum $name {}
            impl Modulo for $name {
                const N: u32 = $modulo;
                const PRIM_ROOT: u32 = $prim_root;
            }
        )*
    };
}

// https://www.mathenachia.blog/ntt-mod-list-01/
impl_modulo!(
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
