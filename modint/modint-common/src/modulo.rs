use std::{fmt::Debug, marker};

pub trait Modulo: Clone + marker::Copy + PartialEq + Eq + Debug {
    const MOD: u32;
    // MOD * MOD_INV = 1 mod R
    const MOD_INV: u32 = {
        let inv = Self::MOD.wrapping_mul(2u32.wrapping_sub(Self::MOD.wrapping_mul(Self::MOD)));
        let inv = inv.wrapping_mul(2u32.wrapping_sub(Self::MOD.wrapping_mul(inv)));
        let inv = inv.wrapping_mul(2u32.wrapping_sub(Self::MOD.wrapping_mul(inv)));
        let inv = inv.wrapping_mul(2u32.wrapping_sub(Self::MOD.wrapping_mul(inv)));
        inv.wrapping_mul(2u32.wrapping_sub(Self::MOD.wrapping_mul(inv)))
    };
    // R = 2^32 mod MOD
    const R: u32 = ((1u64 << 32) % Self::MOD as u64) as u32;
    // R2 = 2^64 mod MOD
    const R2: u32 = ((Self::MOD as u64).wrapping_neg() % Self::MOD as u64) as u32;
    const PRIM_ROOT: u32;
}

macro_rules! impl_modulo {
    ( $({ $name:ident, $modulo:literal, $prim_root:literal },)* ) => {
        $(
            #[derive(Debug, Clone, marker::Copy, PartialEq, Eq)]
            pub enum $name {}
            impl Modulo for $name {
                const MOD: u32 = $modulo;
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
