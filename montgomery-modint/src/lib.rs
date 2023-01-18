mod consts;

pub use consts::*;

use numeric::{One, Zero};
use std::convert::From;
use std::num::ParseIntError;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};
use std::str::FromStr;

#[inline]
const fn mod_pow(a: u32, mut n: u32, p: u32) -> u32 {
    let (mut val, mut res) = (a, 1);
    while n > 0 {
        if n & 1 == 1 {
            res = (res as u64 * val as u64 % p as u64) as u32;
        }
        val = (val as u64 * val as u64 % p as u64) as u32;
        n >>= 1;
    }
    res
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// MontgomeryModint
////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MontgomeryModint<const MOD: u32> {
    pub val: u32,
}

impl<const MOD: u32> MontgomeryModint<MOD> {
    const MOD: u32 = MOD;
    // MOD * MOD_INV = 1 mod R
    const MOD_INV: u32 = {
        let (mut prev, mut inv) = (0, Self::MOD);
        while prev != inv {
            prev = inv;
            inv = inv.wrapping_mul(2u32.wrapping_sub(Self::MOD.wrapping_mul(inv)));
        }
        inv
    };
    // R = 2^32 mod MOD
    const R: u32 = ((1u64 << 32) % Self::MOD as u64) as u32;
    // R2 = 2^64 mod MOD
    const R2: u32 = ((Self::MOD as u64).wrapping_neg() % Self::MOD as u64) as u32;
    const PRIM_ROOT: u32 = match Self::MOD {
        2 => 1,
        167_772_161 => 3,
        469_762_049 => 3,
        754_974_721 => 11,
        998_244_353 => 3,
        _ => {
            let mut x = (Self::MOD - 1) >> (Self::MOD).trailing_zeros();
            let (count, factors) = {
                let mut factors = [2; 20];
                let (mut count, mut i) = (1, 3);
                while (i as u64 * i as u64) <= Self::MOD as u64 {
                    if x % i == 0 {
                        factors[count] = i;
                        count += 1;
                        while x % i == 0 {
                            x /= i;
                        }
                    }
                    i += 2;
                }
                if x > 1 {
                    factors[count] = x;
                    count += 1;
                }
                (count, factors)
            };

            let mut g = 2;
            'main: loop {
                let mut i = 0;
                while i < count {
                    if mod_pow(g, (Self::MOD - 1) / factors[i], Self::MOD) == 1 {
                        g += 1;
                        continue 'main;
                    }
                    i += 1;
                }
                break g;
            }
        }
    };

    // t <- MR(T) = floor(T/R) - floor((TN' mod R)*N/R)
    //  if t < 0 then return t + N else return t
    //      T := a (0 <= T < NR)
    //      N := MOD
    //      N':= MOD_INV    NN' = 1 (mod R)
    //      R := R
    const fn montgomery_reduction(val: u32) -> u32 {
        let (t, f) = (((val.wrapping_mul(Self::MOD_INV) as u64).wrapping_mul(Self::MOD as u64) >> 32) as u32).overflowing_neg();
        if f {
            t.wrapping_add(Self::MOD)
        } else {
            t
        }
    }

    const fn montgomery_multiplication(lhs: u32, rhs: u32) -> u32 {
        let a = lhs as u64 * rhs as u64;
        let (t, f) = ((a >> 32) as u32).overflowing_sub((((a as u32).wrapping_mul(Self::MOD_INV) as u64).wrapping_mul(Self::MOD as u64) >> 32) as u32);
        if f {
            t.wrapping_add(Self::MOD)
        } else {
            t
        }
    }

    #[inline]
    pub const fn new(val: u32) -> Self { Self::raw(val.rem_euclid(Self::MOD)) }

    pub const fn raw(val: u32) -> Self {
        let val = Self::montgomery_multiplication(val, Self::R2);
        Self { val }
    }

    #[inline]
    pub const fn from_mont_expr(val: u32) -> Self { Self { val } }

    #[inline]
    pub const fn val(&self) -> u32 { Self::montgomery_reduction(self.val) }

    #[inline]
    pub const fn val_mont_expr(&self) -> u32 { self.val }

    #[inline]
    pub const fn one() -> Self { Self { val: Self::R } }

    #[inline]
    pub const fn zero() -> Self { Self { val: 0 } }

    pub const fn pow(&self, mut n: u32) -> Self {
        let mut val = self.val;
        let mut res = Self::R;
        while n != 0 {
            if n & 1 != 0 {
                res = Self::montgomery_multiplication(res, val);
            }
            val = Self::montgomery_multiplication(val, val);
            n >>= 1;
        }
        Self { val: res }
    }

    #[inline]
    pub const fn nth_root(n: u32) -> Self {
        debug_assert!(n == 1 << n.trailing_zeros());

        MontgomeryModint::new(Self::PRIM_ROOT).pow(Self::MOD - 1 + (Self::MOD - 1) / n)
    }

    #[inline]
    pub const fn inv(&self) -> Self { self.pow(Self::MOD - 2) }

    #[inline]
    pub const fn add_const(self, rhs: Self) -> Self {
        let (t, fa) = self.val.overflowing_add(rhs.val);
        let (u, fs) = t.overflowing_sub(Self::MOD);
        Self { val: if fa || !fs { u } else { t } }
    }

    #[inline]
    pub const fn sub_const(self, rhs: Self) -> Self {
        let (val, f) = self.val.overflowing_sub(rhs.val);
        Self { val: if f { val.wrapping_add(Self::MOD) } else { val } }
    }

    #[inline]
    pub const fn mul_const(self, rhs: Self) -> Self { Self { val: Self::montgomery_multiplication(self.val, rhs.val) } }

    #[inline]
    pub const fn div_const(self, rhs: Self) -> Self { self.mul_const(rhs.inv()) }
}

impl<const MOD: u32> One for MontgomeryModint<MOD> {
    #[inline]
    fn one() -> Self { Self::one() }
}

impl<const MOD: u32> Zero for MontgomeryModint<MOD> {
    #[inline]
    fn zero() -> Self { Self::zero() }
}

impl<const MOD: u32> Add for MontgomeryModint<MOD> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output { self.add_const(rhs) }
}

impl<const MOD: u32> Sub for MontgomeryModint<MOD> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output { self.sub_const(rhs) }
}

impl<const MOD: u32> Mul for MontgomeryModint<MOD> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output { self.mul_const(rhs) }
}

impl<const MOD: u32> Div for MontgomeryModint<MOD> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output { self.div_const(rhs) }
}

impl<const MOD: u32> AddAssign for MontgomeryModint<MOD> {
    fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<const MOD: u32> SubAssign for MontgomeryModint<MOD> {
    fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<const MOD: u32> MulAssign for MontgomeryModint<MOD> {
    fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<const MOD: u32> DivAssign for MontgomeryModint<MOD> {
    fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl<const MOD: u32> std::fmt::Debug for MontgomeryModint<MOD> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.val()) }
}

impl<const MOD: u32> std::fmt::Display for MontgomeryModint<MOD> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.val()) }
}

impl<const MOD: u32> From<u32> for MontgomeryModint<MOD> {
    fn from(value: u32) -> Self { Self::new(value) }
}

impl<const MOD: u32> From<u64> for MontgomeryModint<MOD> {
    fn from(value: u64) -> Self { Self::raw(value.rem_euclid(Self::MOD as u64) as u32) }
}

impl<const MOD: u32> From<i32> for MontgomeryModint<MOD> {
    fn from(value: i32) -> Self { Self::raw(value.rem_euclid(Self::MOD as i32) as u32) }
}

impl<const MOD: u32> From<i64> for MontgomeryModint<MOD> {
    fn from(value: i64) -> Self { Self::raw(value.rem_euclid(Self::MOD as i64) as u32) }
}

impl<const MOD: u32> FromStr for MontgomeryModint<MOD> {
    type Err = ParseIntError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let neg = s.starts_with("-");

        let val = if neg {
            s[1..].bytes().fold(0u64, |s, v| s * 10 + (v - b'0') as u64)
        } else {
            s.bytes().fold(0u64, |s, v| s * 10 + (v - b'0') as u64)
        };

        if !neg && val < Self::MOD as u64 {
            Ok(Self::raw(val as u32))
        } else if neg {
            Ok(Self::from(-(val as i64)))
        } else {
            Ok(Self::from(val))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::consts::{MOD1000000007, MOD998244353};
    use super::MontgomeryModint;

    type Modint = MontgomeryModint<MOD998244353>;

    #[test]
    fn constant_value_test() {
        assert_eq!(Modint::MOD, 998244353);
        assert_eq!(Modint::MOD.wrapping_mul(Modint::MOD_INV), 1);
        assert_eq!(Modint::R, 301989884);
        assert_eq!(Modint::R2, 932051910);
        assert_eq!(Modint::PRIM_ROOT, 3);

        assert_eq!(MontgomeryModint::<MOD1000000007>::PRIM_ROOT, 5);
    }

    #[test]
    fn montgomery_modint_test() {
        assert_eq!(Modint::zero().val(), 0);
        assert_eq!(Modint::one().val(), 1);
        assert_eq!(Modint::new(10).val(), 10);

        const A: u32 = 347384953;
        const B: u32 = 847362948;
        let a = Modint::new(A);
        let b = Modint::new(B);
        assert_eq!((a + b).val(), 196503548);
        assert_eq!((a - b).val(), 498266358);
        assert_eq!((a * b).val(), (A as u64 * B as u64 % Modint::MOD as u64) as u32);
        assert_eq!(a.pow(B).val(), 860108694);
        assert_eq!((a / b).val(), 748159151);

        assert_eq!("347384953".parse::<Modint>(), Ok(Modint::new(347384953)));
        assert_eq!("-347384953".parse::<Modint>(), Ok(Modint::from(-347384953i64)));
    }
}
