use numeric::{One, Zero};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

pub const MOD_CONST_998244353: u32 = 998244353;

#[inline]
const fn mod_pow(a: u32, mut n: u32, p: u32) -> u32 {
    let (mut val, mut res) = (a, 1);
    while n > 0 {
        if n & 1 == 1 {
            res = (res * val) % p;
        }
        val = (val * val) % p;
        n >>= 1;
    }
    res
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MontgomeryModintu32<const MOD: u32> {
    val: u32,
}

impl<const MOD: u32> MontgomeryModintu32<MOD> {
    pub const MOD: u32 = MOD;
    // MOD * MOD_INV = -1 mod R
    // f(x) = 1/x - a
    //      f(x) = 0 <=> x = 1/a
    // x[n+1] = x[n] - f(x[n])/f'(x[n])
    //        = x[n] - (1/x[n] - a) / (-1/(x[n]^2))
    //        = 2*x[n] - a*x[n]
    pub const MOD_INV: u32 = {
        let (mut prev, mut inv) = (0, Self::MOD);
        while prev != inv {
            prev = inv;
            inv = inv.wrapping_mul(2u32.wrapping_sub(Self::MOD.wrapping_mul(inv)));
        }
        inv.wrapping_neg()
    };
    // R = 2^32 mod 998244353
    pub const R: u32 = ((1u64 << 32) % Self::MOD as u64) as u32;
    // R2 = 2^32 (mod MOD)
    // R^2 = R^2 - MOD (mod MOD)
    //      (R^2 - MOD) (64bit) = (-MOD) (64bit)
    pub const R2: u32 = ((Self::MOD as u64).wrapping_neg() % Self::MOD as u64) as u32;
    pub const PRIM_ROOT: u32 = match Self::MOD {
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
            loop {
                let mut bad = false;
                let mut i = 0;
                while i < count {
                    if mod_pow(g, (Self::MOD - 1) / factors[i], Self::MOD) == 1 {
                        bad = true;
                        break;
                    }
                    i += 1;
                }
                if !bad {
                    break g;
                }
                g += 1;
            }
        }
    };

    #[inline]
    // t <- MR(T) = (T + (TN' mod R) * N) / R
    //  if t >= N then return t - N else return t
    //      T := a (0 <= T < NR)
    //      N := modulo()
    //      N':= montgomery_constant_modulo_inv()
    //      R := montgomery_constant_r()
    const fn montgomery_reduction(t: u32) -> u32 {
        let t = ((t as u64).wrapping_add((t.wrapping_mul(Self::MOD_INV) as u64).wrapping_mul(Self::MOD as u64)) >> 32) as u32;
        if t >= Self::MOD {
            t - Self::MOD
        } else {
            t
        }
    }

    #[inline]
    const fn multiplication(lhs: u32, rhs: u32) -> u32 {
        let a = lhs as u64 * rhs as u64;
        let t = (a.wrapping_add(((a as u32).wrapping_mul(Self::MOD_INV) as u64).wrapping_mul(Self::MOD as u64)) >> 32) as u32;
        if t >= Self::MOD {
            t - Self::MOD
        } else {
            t
        }
    }

    #[inline]
    pub const fn raw(val: u32) -> Self {
        let val = Self::multiplication(val, Self::R2);
        Self { val }
    }

    #[inline]
    pub const fn new(val: u32) -> Self { Self::raw(val % Self::MOD) }

    #[inline]
    pub const fn from_mont_expr(val: u32) -> Self { Self { val } }

    #[inline]
    pub const fn new_u64(val: u64) -> Self { Self::raw((val % Self::MOD as u64) as u32) }

    #[inline]
    pub const fn new_i32(val: i32) -> Self { Self::new_i64(val as i64) }

    #[inline]
    pub const fn new_i64(val: i64) -> Self { Self::raw(val.rem_euclid(Self::MOD as i64) as u32) }

    #[inline]
    pub const fn val(&self) -> u32 { Self::montgomery_reduction(self.val) }

    #[inline]
    pub const fn val_mont_expr(&self) -> u32 { self.val }

    #[inline]
    pub const fn one() -> Self { Self { val: Self::R } }

    #[inline]
    pub const fn zero() -> Self { Self { val: 0 } }

    #[inline]
    pub const fn pow(&self, mut n: u32) -> Self {
        let mut val = self.val;
        let mut res = if (n & 1) != 0 { val } else { Self::R };
        n >>= 1;
        while n != 0 {
            val = Self::multiplication(val, val);
            if n & 1 != 0 {
                res = Self::multiplication(res, val);
            }
            n >>= 1;
        }
        Self { val: res }
    }

    #[inline]
    pub const fn nth_root(n: u32) -> Self {
        debug_assert!(n == 1 << n.trailing_zeros());

        MontgomeryModintu32::new(Self::PRIM_ROOT).pow(Self::MOD - 1 + (Self::MOD - 1) / n)
    }

    #[inline]
    pub const fn inv(&self) -> Self { self.pow(Self::MOD - 2) }

    #[inline]
    const fn add_mont(&self, rhs: Self) -> Self {
        let (t, fa) = self.val.overflowing_add(rhs.val);
        let (u, fs) = t.overflowing_sub(Self::MOD);
        Self {
            val: if fa || !fs { u } else { t },
        }
    }

    #[inline]
    const fn sub_mont(&self, rhs: Self) -> Self {
        let (val, f) = self.val.overflowing_sub(rhs.val);
        Self {
            val: if f { val.wrapping_add(Self::MOD) } else { val },
        }
    }

    #[inline]
    const fn mul_mont(&self, rhs: Self) -> Self {
        Self {
            val: Self::multiplication(self.val, rhs.val),
        }
    }

    #[inline]
    const fn div_mont(&self, rhs: Self) -> Self { self.mul_mont(rhs.inv()) }
}

impl<const MOD: u32> One for MontgomeryModintu32<MOD> {
    #[inline]
    fn one() -> Self { Self::one() }
}

impl<const MOD: u32> Zero for MontgomeryModintu32<MOD> {
    #[inline]
    fn zero() -> Self { Self::zero() }
}

impl<const MOD: u32> Add for MontgomeryModintu32<MOD> {
    type Output = Self;
    #[inline]
    fn add(self, rhs: Self) -> Self::Output { self.add_mont(rhs) }
}

impl<const MOD: u32> Sub for MontgomeryModintu32<MOD> {
    type Output = Self;
    #[inline]
    fn sub(self, rhs: Self) -> Self::Output { self.sub_mont(rhs) }
}

impl<const MOD: u32> Mul for MontgomeryModintu32<MOD> {
    type Output = Self;
    #[inline]
    fn mul(self, rhs: Self) -> Self::Output { self.mul_mont(rhs) }
}

impl<const MOD: u32> Div for MontgomeryModintu32<MOD> {
    type Output = Self;
    #[inline]
    fn div(self, rhs: Self) -> Self::Output { self.div_mont(rhs) }
}

impl<const MOD: u32> AddAssign for MontgomeryModintu32<MOD> {
    #[inline]
    fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<const MOD: u32> SubAssign for MontgomeryModintu32<MOD> {
    #[inline]
    fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<const MOD: u32> MulAssign for MontgomeryModintu32<MOD> {
    #[inline]
    fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<const MOD: u32> DivAssign for MontgomeryModintu32<MOD> {
    #[inline]
    fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl<const MOD: u32> std::fmt::Debug for MontgomeryModintu32<MOD> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.val()) }
}

impl<const MOD: u32> std::fmt::Display for MontgomeryModintu32<MOD> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.val()) }
}

#[cfg(test)]
mod tests {
    use super::{MontgomeryModintu32, MOD_CONST_998244353};

    #[test]
    fn constant_value_test() {
        type Modint = MontgomeryModintu32<MOD_CONST_998244353>;
        assert_eq!(Modint::MOD, 998244353);
        assert_eq!(Modint::MOD_INV, 998244351);
        assert_eq!(Modint::R, 301989884);
        assert_eq!(Modint::R2, 932051910);
        assert_eq!(Modint::PRIM_ROOT, 3);
    }
}
