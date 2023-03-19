use iolib::{FastInput, Readable};
pub use modint_common::*;
use numeric::{One, Zero};
use std::convert::From;
use std::marker::PhantomData;
use std::num::ParseIntError;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::str::FromStr;

////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// MontgomeryModint
////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MontgomeryModint<M: Modulo> {
    pub val: u32,
    _phantom: PhantomData<fn() -> M>,
}

impl<M: Modulo> MontgomeryModint<M> {
    // t <- MR(T) = floor(T/R) - floor((TN' mod R)*N/R)
    //  if t < 0 then return t + N else return t
    //      T := a (0 <= T < NR)
    //      N := MOD
    //      N':= MOD_INV    NN' = 1 (mod R)
    //      R := R
    fn montgomery_reduction(val: u32) -> u32 {
        let (t, f) = (((val.wrapping_mul(M::MOD_INV) as u64).wrapping_mul(M::MOD as u64) >> 32) as u32).overflowing_neg();
        t.wrapping_add(M::MOD * f as u32)
    }

    fn montgomery_multiplication(lhs: u32, rhs: u32) -> u32 {
        let a = lhs as u64 * rhs as u64;
        let (t, f) = ((a >> 32) as u32).overflowing_sub((((a as u32).wrapping_mul(M::MOD_INV) as u64).wrapping_mul(M::MOD as u64) >> 32) as u32);
        t.wrapping_add(M::MOD * f as u32)
    }

    #[inline]
    pub fn new(val: u32) -> Self { Self::raw(val.rem_euclid(M::MOD)) }

    pub fn raw(val: u32) -> Self {
        let val = Self::montgomery_multiplication(val, M::R2);
        Self { val, _phantom: PhantomData }
    }

    #[inline]
    pub fn from_mont_expr(val: u32) -> Self { Self { val, _phantom: PhantomData } }

    #[inline]
    pub fn val(&self) -> u32 { Self::montgomery_reduction(self.val) }

    #[inline]
    pub fn val_mont_expr(&self) -> u32 { self.val }

    #[inline]
    pub fn one() -> Self { Self { val: M::R, _phantom: PhantomData } }

    #[inline]
    pub fn zero() -> Self { Self { val: 0, _phantom: PhantomData } }

    pub fn pow(&self, mut n: u64) -> Self {
        let mut val = self.val;
        let mut res = M::R;
        while n != 0 {
            if n & 1 != 0 {
                res = Self::montgomery_multiplication(res, val);
            }
            val = Self::montgomery_multiplication(val, val);
            n >>= 1;
        }
        Self { val: res, _phantom: PhantomData }
    }

    #[inline]
    pub fn nth_root(n: u32) -> Self {
        debug_assert!(n == 1 << n.trailing_zeros());

        MontgomeryModint::<M>::new(M::PRIM_ROOT).pow(M::MOD as u64 - 1 + (M::MOD as u64 - 1) / n as u64)
    }

    #[inline]
    pub fn inv(&self) -> Self { self.pow(M::MOD as u64 - 2) }
}

impl<M: Modulo> One for MontgomeryModint<M> {
    #[inline]
    fn one() -> Self { Self::one() }
}

impl<M: Modulo> Zero for MontgomeryModint<M> {
    #[inline]
    fn zero() -> Self { Self::zero() }
}

impl<M: Modulo> Add for MontgomeryModint<M> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        let (t, fa) = self.val.overflowing_add(rhs.val);
        let (u, fs) = t.overflowing_sub(M::MOD);
        Self { val: if fa || !fs { u } else { t }, _phantom: PhantomData }
    }
}

impl<M: Modulo> Sub for MontgomeryModint<M> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        let (val, f) = self.val.overflowing_sub(rhs.val);
        Self {
            val: if f { val.wrapping_add(M::MOD) } else { val },
            _phantom: PhantomData,
        }
    }
}

impl<M: Modulo> Mul for MontgomeryModint<M> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            val: Self::montgomery_multiplication(self.val, rhs.val),
            _phantom: PhantomData,
        }
    }
}

impl<M: Modulo> Div for MontgomeryModint<M> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output { self * rhs.inv() }
}

impl<M: Modulo> Neg for MontgomeryModint<M> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        if self.val == 0 {
            self
        } else {
            Self { val: M::MOD - self.val, _phantom: PhantomData }
        }
    }
}

impl<M: Modulo> AddAssign for MontgomeryModint<M> {
    fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<M: Modulo> SubAssign for MontgomeryModint<M> {
    fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<M: Modulo> MulAssign for MontgomeryModint<M> {
    fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<M: Modulo> DivAssign for MontgomeryModint<M> {
    fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl<M: Modulo> std::fmt::Debug for MontgomeryModint<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.val()) }
}

impl<M: Modulo> std::fmt::Display for MontgomeryModint<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.val()) }
}

impl<M: Modulo> From<u32> for MontgomeryModint<M> {
    fn from(value: u32) -> Self { Self::new(value) }
}

impl<M: Modulo> From<u64> for MontgomeryModint<M> {
    fn from(value: u64) -> Self { Self::raw(value.rem_euclid(M::MOD as u64) as u32) }
}

impl<M: Modulo> From<i32> for MontgomeryModint<M> {
    fn from(value: i32) -> Self { Self::raw(value.rem_euclid(M::MOD as i32) as u32) }
}

impl<M: Modulo> From<i64> for MontgomeryModint<M> {
    fn from(value: i64) -> Self { Self::raw(value.rem_euclid(M::MOD as i64) as u32) }
}

impl<M: Modulo> FromStr for MontgomeryModint<M> {
    type Err = ParseIntError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let neg = s.starts_with("-");

        let val = if neg {
            s[1..].bytes().fold(0u64, |s, v| s * 10 + (v - b'0') as u64)
        } else {
            s.bytes().fold(0u64, |s, v| s * 10 + (v - b'0') as u64)
        };

        if !neg && val < M::MOD as u64 {
            Ok(Self::raw(val as u32))
        } else if neg {
            Ok(Self::from(-(val as i64)))
        } else {
            Ok(Self::from(val))
        }
    }
}

impl<M: Modulo> Readable for MontgomeryModint<M> {
    fn read(src: &mut FastInput) -> Self { MontgomeryModint::from(u32::read(src)) }
}

#[cfg(test)]
mod tests {
    use super::MontgomeryModint;
    use modint_common::{Mod4194304001, Mod998244353, Modulo};

    #[test]
    fn constant_value_test() {
        assert_eq!(Mod998244353::MOD, 998244353);
        assert_eq!(Mod998244353::MOD.wrapping_mul(Mod998244353::MOD_INV), 1);
        assert_eq!(Mod998244353::R, 301989884);
        assert_eq!(Mod998244353::R2, 932051910);
        assert_eq!(Mod998244353::PRIM_ROOT, 3);
    }

    #[test]
    fn montgomery_modint_test() {
        type Modint = MontgomeryModint<Mod998244353>;

        assert_eq!(Mod998244353::R, 301989884);
        assert_eq!(Mod998244353::MOD.wrapping_mul(Mod998244353::MOD_INV), 1);
        assert_eq!(Mod998244353::R2, 932051910);

        assert_eq!(Modint::zero().val(), 0);
        assert_eq!(Modint::one().val(), 1);
        assert_eq!(Modint::new(10).val(), 10);

        const A: u32 = 347384953;
        const B: u32 = 847362948;
        let a = Modint::new(A);
        let b = Modint::new(B);
        assert_eq!((a + b).val(), 196503548);
        assert_eq!((a - b).val(), 498266358);
        assert_eq!((a * b).val(), (A as u64 * B as u64 % Mod998244353::MOD as u64) as u32);
        assert_eq!(a.pow(B as u64).val(), 860108694);
        assert_eq!((a / b).val(), 748159151);
        assert_eq!((-a).val(), (Modint::zero() - a).val());

        assert_eq!("347384953".parse::<Modint>(), Ok(Modint::new(347384953)));
        assert_eq!("-347384953".parse::<Modint>(), Ok(Modint::from(-347384953i64)));
    }

    #[test]
    fn montgomery_modint_large_mod_test() {
        type Modint = MontgomeryModint<Mod4194304001>;

        assert_eq!(Modint::zero().val(), 0u32);
        assert_eq!(Modint::one().val(), 1u32);
        assert_eq!(Modint::new(10).val(), 10u32);

        const A: u32 = 347384953;
        const B: u32 = 847362948;
        let a = Modint::new(A);
        let b = Modint::new(B);
        assert_eq!((a + b).val(), 1194747901u32);
        assert_eq!((a - b).val(), 3694326006u32);
        assert_eq!((a * b).val(), (A as u64 * B as u64 % Mod4194304001::MOD as u64) as u32);
        assert_eq!(a.pow(B as u64).val(), 101451096u32);
        assert_eq!((a / b).val(), 3072607503);
    }
}
