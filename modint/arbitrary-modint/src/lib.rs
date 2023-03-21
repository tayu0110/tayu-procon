use std::{
    cell::RefCell,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign},
};

thread_local! {
    static MOD: RefCell<u64> = RefCell::new(998244353);
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// ArbitraryModint
////////////////////////////////////////////////////////////////////////////////////////////////////////////
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ArbitraryModint {
    val: u64,
}

impl ArbitraryModint {
    #[inline]
    pub fn new(val: u64) -> Self { Self::raw(val % Self::modulo()) }

    #[inline]
    pub fn raw(val: u64) -> Self { Self { val } }

    #[inline]
    pub fn one() -> Self { Self::new(1) }

    #[inline]
    pub fn zero() -> Self { Self::raw(0) }

    #[inline]
    pub fn modulo() -> u64 { MOD.with(|v| *v.borrow()) }

    #[inline]
    #[allow(const_item_mutation)]
    pub fn set_modulo(modulo: u64) { MOD.with(|v| *v.borrow_mut() = modulo) }

    #[inline]
    pub fn add_raw(&self, rhs: u64) -> Self {
        let (t, fa) = self.val.overflowing_add(rhs);
        let (u, fs) = t.overflowing_sub(Self::modulo());
        let f = fa as u64 | !fs as u64;
        Self { val: f * u + (1 - f) * t }
    }

    #[inline]
    pub fn sub_raw(&self, rhs: u64) -> Self {
        let (val, f) = self.val.overflowing_sub(rhs);
        Self { val: val.wrapping_add(Self::modulo() * f as u64) }
    }

    #[inline]
    pub fn mul_raw(&self, rhs: u64) -> Self {
        Self {
            val: (self.val as u128 * rhs as u128 % Self::modulo() as u128) as u64,
        }
    }

    #[inline]
    pub fn pow(&self, mut exp: u64) -> Self {
        let (mut val, mut res) = (self.val as u64, 1);
        while exp > 0 {
            if exp & 1 == 1 {
                res = (res as u128 * val as u128 % Self::modulo() as u128) as u64;
            }
            val = (val as u128 * val as u128 % Self::modulo() as u128) as u64;
            exp >>= 1;
        }
        Self { val: res }
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
        let (mut s, mut ys) = (Self::modulo(), 0u64);
        let (mut t, mut yt) = (self.val, 1u64);
        while s % t != 0 {
            let tmp = s / t;
            let u = s - t * tmp;

            let (v, f) = yt.overflowing_mul(tmp);
            let yu = if f || v >= Self::modulo() { ys.wrapping_add(yt.wrapping_neg() * tmp) } else { ys.wrapping_sub(v) };

            s = t;
            ys = yt;
            t = u;
            yt = yu;
        }

        if yt > Self::modulo() {
            yt = yt.wrapping_add(Self::modulo());
        }

        assert_eq!(t, 1);
        assert_eq!(self.val as u128 * yt as u128 % Self::modulo() as u128, 1);

        Self { val: yt }
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
        const A: u64 = 347384953;
        const B: u64 = 847362948;

        ArbitraryModint::set_modulo(998244353);
        let ma: ArbitraryModint = ArbitraryModint::new(A);
        let mb: ArbitraryModint = ArbitraryModint::new(B);

        let ma_inv = ma.inv();
        let mb_inv = mb.inv();

        assert!(ma_inv.val < ArbitraryModint::modulo());
        assert_eq!(ma.val * ma_inv.val % ArbitraryModint::modulo(), 1);
        assert_eq!(mb.val * mb_inv.val % ArbitraryModint::modulo(), 1);
        assert_eq!((ma + mb).val, 196503548);
        assert_eq!((ma - mb).val, 498266358);
        assert_eq!((ma * mb).val, 17486571);
        assert_eq!((ma / mb).val, 748159151);
        assert_eq!(ma.add_raw(B).val, 196503548);
        assert_eq!(ma.sub_raw(B).val, 498266358);
        assert_eq!(ma.mul_raw(B).val, 17486571);
        assert_eq!(ma.pow(B).val, 860108694);
    }

    #[test]
    fn dynamic_modint_test_big_prime() {
        const MOD: u64 = 4570400481202625717;
        const A: u64 = 48375902915869447;
        const B: u64 = 98372873839201592;

        ArbitraryModint::set_modulo(MOD);
        let ma: ArbitraryModint = ArbitraryModint::new(A);
        let mb: ArbitraryModint = ArbitraryModint::new(B);

        let ma_inv = ma.inv();
        let mb_inv = mb.inv();

        assert_eq!(ArbitraryModint::modulo(), MOD);
        assert_eq!((ma * ma_inv).val, 1);
        assert_eq!((mb * mb_inv).val, 1);
        assert_eq!((ma + mb).val, (A + B) % MOD);
        assert_eq!((ma - mb).val, (A + MOD - B) % MOD);
        assert_eq!((ma * mb).val, (A as u128 * B as u128 % MOD as u128) as u64);
        assert_eq!((ma / mb).val, (A as u128 * mb_inv.val as u128 % MOD as u128) as u64);
        assert_eq!(ma.add_raw(B).val, (A + B) % MOD);
        assert_eq!(ma.sub_raw(B).val, (A + MOD - B) % MOD);
        assert_eq!(ma.mul_raw(B).val, (A as u128 * B as u128 % MOD as u128) as u64);
        assert_eq!(ma.pow(B).val, 2247504130363815882);
    }
}
