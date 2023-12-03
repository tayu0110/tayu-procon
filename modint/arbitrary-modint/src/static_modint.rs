use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// ArbitraryStaticModint
////////////////////////////////////////////////////////////////////////////////////////////////////////////
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArbitraryStaticModint<const MOD: u64> {
    val: u64,
}

impl<const MOD: u64> ArbitraryStaticModint<MOD> {
    const MOD: u64 = {
        debug_assert!(MOD != 0);
        MOD
    };

    #[inline]
    pub const fn new(val: u64) -> Self {
        Self::raw(val % Self::MOD)
    }

    #[inline]
    pub const fn raw(val: u64) -> Self {
        Self { val }
    }

    #[inline]
    pub const fn one() -> Self {
        Self::new(1)
    }

    #[inline]
    pub const fn zero() -> Self {
        Self::raw(0)
    }

    #[inline]
    pub const fn val(self) -> u64 {
        self.val
    }

    #[inline]
    pub const fn modulo() -> u64 {
        Self::MOD
    }

    #[inline]
    pub const fn add_raw(&self, rhs: u64) -> Self {
        let (t, fa) = self.val.overflowing_add(rhs);
        let (u, fs) = t.overflowing_sub(Self::MOD);
        let f = fa as u64 | !fs as u64;
        Self { val: f * u + (1 - f) * t }
    }

    #[inline]
    pub const fn sub_raw(&self, rhs: u64) -> Self {
        let (val, f) = self.val.overflowing_sub(rhs);
        Self { val: val.wrapping_add(Self::MOD * f as u64) }
    }

    #[inline]
    pub const fn mul_raw(&self, rhs: u64) -> Self {
        Self {
            val: (self.val as u128 * rhs as u128 % Self::MOD as u128) as u64,
        }
    }

    #[inline]
    pub const fn pow(self, mut exp: u64) -> Self {
        let (mut val, mut res) = (self, Self::one());
        while exp > 0 {
            if exp & 1 == 1 {
                res = res.mul_raw(val.val);
            }
            val = val.mul_raw(val.val);
            exp >>= 1;
        }
        res
    }

    #[inline]
    //  modulo * 1 + val * 0 = modulo    ...(1)  (xs = 1, ys = 0)
    //  modulo * 0 + val * 1 = val       ...(2)  (xt = 0, yt = 1)
    //       -> (1) - (2) * |modulo/val|
    //       -> modulo * (xs - xt * |modulo/val|) + val * (ys - yt * |modulo/val|) = modulo % val
    // Repeating this, the right-hand side becomes gcd(modulo, val)
    //  modulo * xt + val * yt = gcd(modulo, val)
    // So, if gcd(modulo, val) is 1, val * yt = 1 (mod modulo)  -> yt = val^{-1} (mod modulo)
    pub const fn inv(&self) -> Self {
        let (mut s, mut ys) = (Self::MOD, 0u64);
        let (mut t, mut yt) = (self.val, 1u64);
        while s % t != 0 {
            let tmp = s / t;
            let u = s - t * tmp;

            let (v, f) = yt.overflowing_mul(tmp);
            let yu = if f || v >= Self::MOD {
                ys.wrapping_add(yt.wrapping_neg() * tmp)
            } else {
                ys.wrapping_sub(v)
            };

            s = t;
            ys = yt;
            t = u;
            yt = yu;
        }

        if yt > Self::MOD {
            yt = yt.wrapping_add(Self::MOD);
        }

        assert!(t == 1);
        assert!(self.val as u128 * yt as u128 % Self::MOD as u128 == 1);

        Self { val: yt }
    }
}

impl<const MOD: u64> std::fmt::Debug for ArbitraryStaticModint<MOD> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl<const MOD: u64> std::fmt::Display for ArbitraryStaticModint<MOD> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl<const MOD: u64> Add for ArbitraryStaticModint<MOD> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        self.add_raw(rhs.val)
    }
}

impl<const MOD: u64> AddAssign for ArbitraryStaticModint<MOD> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<const MOD: u64> Sub for ArbitraryStaticModint<MOD> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        self.sub_raw(rhs.val)
    }
}

impl<const MOD: u64> SubAssign for ArbitraryStaticModint<MOD> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<const MOD: u64> Mul for ArbitraryStaticModint<MOD> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        self.mul_raw(rhs.val)
    }
}

impl<const MOD: u64> MulAssign for ArbitraryStaticModint<MOD> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<const MOD: u64> Div for ArbitraryStaticModint<MOD> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        debug_assert!(rhs.val != 0);
        self * rhs.inv()
    }
}

impl<const MOD: u64> DivAssign for ArbitraryStaticModint<MOD> {
    fn div_assign(&mut self, rhs: Self) {
        debug_assert!(rhs.val != 0);
        *self *= rhs.inv()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arbitrary_static_modint_test() {
        const A: u64 = 347384953;
        const B: u64 = 847362948;
        const MOD: u64 = 998244353;

        const MA: ArbitraryStaticModint<MOD> = ArbitraryStaticModint::new(A);
        const MB: ArbitraryStaticModint<MOD> = ArbitraryStaticModint::new(B);

        let ma_inv = MA.inv();
        let mb_inv = MB.inv();

        assert!(ma_inv.val < MOD);
        assert_eq!(MA.val * ma_inv.val % MOD, 1);
        assert_eq!(MB.val * mb_inv.val % MOD, 1);
        assert_eq!((MA + MB).val, 196503548);
        assert_eq!((MA - MB).val, 498266358);
        assert_eq!((MA * MB).val, 17486571);
        assert_eq!((MA / MB).val, 748159151);
        assert_eq!(MA.add_raw(B).val, 196503548);
        assert_eq!(MA.sub_raw(B).val, 498266358);
        assert_eq!(MA.mul_raw(B).val, 17486571);
        assert_eq!(MA.pow(B).val, 860108694);
    }

    #[test]
    fn arbitrary_static_modint_test_big_prime() {
        const MOD: u64 = 4570400481202625717;
        const A: u64 = 48375902915869447;
        const B: u64 = 98372873839201592;

        const MA: ArbitraryStaticModint<MOD> = ArbitraryStaticModint::new(A);
        const MB: ArbitraryStaticModint<MOD> = ArbitraryStaticModint::new(B);

        let ma_inv = MA.inv();
        let mb_inv = MB.inv();

        assert_eq!(ArbitraryStaticModint::<MOD>::modulo(), MOD);
        assert_eq!((MA * ma_inv).val, 1);
        assert_eq!((MB * mb_inv).val, 1);
        assert_eq!((MA + MB).val, (A + B) % MOD);
        assert_eq!((MA - MB).val, (A + MOD - B) % MOD);
        assert_eq!((MA * MB).val, (A as u128 * B as u128 % MOD as u128) as u64);
        assert_eq!(
            (MA / MB).val,
            (A as u128 * mb_inv.val as u128 % MOD as u128) as u64
        );
        assert_eq!(MA.add_raw(B).val, (A + B) % MOD);
        assert_eq!(MA.sub_raw(B).val, (A + MOD - B) % MOD);
        assert_eq!(
            MA.mul_raw(B).val,
            (A as u128 * B as u128 % MOD as u128) as u64
        );
        assert_eq!(MA.pow(B).val, 2247504130363815882);
    }
}
