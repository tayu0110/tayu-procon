use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// ArbitraryModint
////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ArbitraryModint {
    val: u64,
    modulo: u64,
}

impl ArbitraryModint {
    #[inline]
    pub const fn new(val: u64, modulo: u64) -> Self { Self::raw(val % modulo, modulo) }

    #[inline]
    pub const fn raw(val: u64, modulo: u64) -> Self { Self { val, modulo } }

    #[inline]
    pub const fn one(modulo: u64) -> Self { Self::new(1, modulo) }

    #[inline]
    pub const fn zero(modulo: u64) -> Self { Self::raw(0, modulo) }

    #[inline]
    pub const fn add_raw(&self, rhs: u64) -> Self {
        let (t, fa) = self.val.overflowing_add(rhs);
        let (u, fs) = t.overflowing_sub(self.modulo);
        let f = fa as u64 | !fs as u64;
        Self { val: f * u + (1 - f) * t, modulo: self.modulo }
    }

    #[inline]
    pub const fn sub_raw(&self, rhs: u64) -> Self {
        let (val, f) = self.val.overflowing_sub(rhs);
        Self {
            val: val.wrapping_add(self.modulo * f as u64),
            modulo: self.modulo,
        }
    }

    #[inline]
    pub const fn mul_raw(&self, rhs: u64) -> Self {
        Self {
            val: (self.val as u128 * rhs as u128 % self.modulo as u128) as u64,
            modulo: self.modulo,
        }
    }

    #[inline]
    pub fn pow(&self, mut exp: u64) -> Self {
        let (mut val, mut res) = (self.val as u64, 1);
        while exp > 0 {
            if exp & 1 == 1 {
                res = (res as u128 * val as u128 % self.modulo as u128) as u64;
            }
            val = (val as u128 * val as u128 % self.modulo as u128) as u64;
            exp >>= 1;
        }
        Self { val: res, modulo: self.modulo }
    }

    #[inline]
    //  modulo * 1 + val * 0 = modulo    ...(1)  (xs = 1, ys = 0)
    //  modulo * 0 + val * 1 = val       ...(2)  (xt = 0, yt = 1)
    //       -> (1) - (2) * |modulo/val|
    //       -> modulo * (xs - xt * |modulo/val|) + val * (ys - yt * |modulo/val|) = modulo % val
    // Repeating this, the right-hand side becomes gcd(modulo, val)
    //  modulo * xt + val * yt = gcd(modulo, val)
    // So, if gcd(modulo, val) is 1, val * yt = 1 (mod modulo)  -> yt = val^{-1} (mod modulo)
    pub fn inv(&self) -> Self {
        let (mut s, mut ys) = (self.modulo, 0u64);
        let (mut t, mut yt) = (self.val, 1u64);
        while s % t != 0 {
            let tmp = s / t;
            let u = s - t * tmp;

            let (v, f) = yt.overflowing_mul(tmp);
            let yu = if f || v >= self.modulo { ys.wrapping_add(yt.wrapping_neg() * tmp) } else { ys.wrapping_sub(v) };

            s = t;
            ys = yt;
            t = u;
            yt = yu;
        }

        if yt > self.modulo {
            yt = yt.wrapping_add(self.modulo);
        }

        assert_eq!(t, 1);
        assert_eq!(self.val as u128 * yt as u128 % self.modulo as u128, 1);

        Self { val: yt, modulo: self.modulo }
    }
}

impl std::fmt::Debug for ArbitraryModint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.val) }
}

impl std::fmt::Display for ArbitraryModint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.val) }
}

impl Add for ArbitraryModint {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output { self.add_raw(rhs.val) }
}

impl AddAssign for ArbitraryModint {
    fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl Sub for ArbitraryModint {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output { self.sub_raw(rhs.val) }
}

impl SubAssign for ArbitraryModint {
    fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl Mul for ArbitraryModint {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output { self.mul_raw(rhs.val) }
}

impl MulAssign for ArbitraryModint {
    fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl Div for ArbitraryModint {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        debug_assert!(rhs.val != 0);
        self * rhs.inv()
    }
}

impl DivAssign for ArbitraryModint {
    fn div_assign(&mut self, rhs: Self) {
        debug_assert!(rhs.val != 0);
        *self *= rhs.inv()
    }
}

#[cfg(test)]
mod tests {
    use super::ArbitraryModint;

    #[test]
    fn dynamic_modint_test() {
        const MOD: u64 = 998244353;
        const A: u64 = 347384953;
        const B: u64 = 847362948;

        const MA: ArbitraryModint = ArbitraryModint::new(A, MOD);
        const MB: ArbitraryModint = ArbitraryModint::new(B, MOD);

        let ma_inv = MA.inv();
        let mb_inv = MB.inv();

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
    fn dynamic_modint_test_big_prime() {
        const MOD: u64 = 4570400481202625717;
        const A: u64 = 48375902915869447;
        const B: u64 = 98372873839201592;

        const MA: ArbitraryModint = ArbitraryModint::new(A, MOD);
        const MB: ArbitraryModint = ArbitraryModint::new(B, MOD);

        let ma_inv = MA.inv();
        let mb_inv = MB.inv();

        assert_eq!((MA * ma_inv).val, 1);
        assert_eq!((MB * mb_inv).val, 1);
        assert_eq!((MA + MB).val, (A + B) % MOD);
        assert_eq!((MA - MB).val, (A + MOD - B) % MOD);
        assert_eq!((MA * MB).val, (A as u128 * B as u128 % MOD as u128) as u64);
        assert_eq!((MA / MB).val, (A as u128 * mb_inv.val as u128 % MOD as u128) as u64);
        assert_eq!(MA.add_raw(B).val, (A + B) % MOD);
        assert_eq!(MA.sub_raw(B).val, (A + MOD - B) % MOD);
        assert_eq!(MA.mul_raw(B).val, (A as u128 * B as u128 % MOD as u128) as u64);
        assert_eq!(MA.pow(B).val, 2247504130363815882);
    }
}
