use std::marker;

pub trait Modulo: Clone + marker::Copy + PartialEq + Eq {
    const MOD: u32;
    // MOD * MOD_INV = -1 mod R
    const MOD_INV: u32 = {
        let inv = Self::MOD.wrapping_mul(2u32.wrapping_sub(Self::MOD.wrapping_mul(Self::MOD)));
        let inv = inv.wrapping_mul(2u32.wrapping_sub(Self::MOD.wrapping_mul(inv)));
        let inv = inv.wrapping_mul(2u32.wrapping_sub(Self::MOD.wrapping_mul(inv)));
        let inv = inv.wrapping_mul(2u32.wrapping_sub(Self::MOD.wrapping_mul(inv)));
        inv.wrapping_neg()
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
            #[derive(Clone, marker::Copy, PartialEq, Eq)]
            pub enum $name {}
            impl Modulo for $name {
                const MOD: u32 = $modulo;
                const PRIM_ROOT: u32 = $prim_root;
            }
        )*
    };
}

impl_modulo!(
    { Mod167772161, 167772161, 3 },
    { Mod469762049, 469762049, 3 },
    { Mod754974721, 754974721, 11 },
    { Mod998244353, 998244353, 3 },
    { Mod1000000007, 1000000007, 5 },
);
