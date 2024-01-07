mod barrett;
mod static_modint;

pub use barrett::*;
pub use static_modint::*;
use std::{
    cell::RefCell,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
};

thread_local! {
    static MOD: RefCell<u64> = RefCell::new(998244353);
    static BARRETT: RefCell<BarrettReduction> = RefCell::new(BarrettReduction::new(998244353));
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// ArbitraryModint
////////////////////////////////////////////////////////////////////////////////////////////////////////////
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
pub struct ArbitraryModint {
    val: u32,
}

impl ArbitraryModint {
    #[inline]
    pub fn new(val: u64) -> Self {
        Self::raw(BARRETT.with(|v| v.borrow().reduce(val)))
    }

    #[inline]
    pub fn raw(val: u32) -> Self {
        Self { val }
    }

    #[inline]
    pub fn val(&self) -> u32 {
        self.val
    }

    #[inline]
    pub fn one() -> Self {
        Self::new(1)
    }

    #[inline]
    pub fn zero() -> Self {
        Self::raw(0)
    }

    #[inline]
    pub fn modulo() -> u32 {
        BARRETT.with(|v| v.borrow().modulo())
    }

    #[inline]
    pub fn set_modulo(modulo: u32) {
        BARRETT.with(|v| *v.borrow_mut() = BarrettReduction::new(modulo))
    }

    #[inline]
    pub fn add_raw(&self, rhs: u32) -> Self {
        let (t, fa) = self.val.overflowing_add(rhs);
        let (u, fs) = t.overflowing_sub(Self::modulo());
        let f = fa as u32 | !fs as u32;
        Self { val: f * u + (1 - f) * t }
    }

    #[inline]
    pub fn sub_raw(&self, rhs: u32) -> Self {
        let (val, f) = self.val.overflowing_sub(rhs);
        Self { val: val.wrapping_add(Self::modulo() * f as u32) }
    }

    #[inline]
    pub fn mul_raw(&self, rhs: u32) -> Self {
        let val = BARRETT.with(|b| b.borrow().reduce(self.val as u64 * rhs as u64));
        Self { val }
    }

    #[inline]
    pub fn pow(&self, mut exp: u64) -> Self {
        let (mut val, mut res) = (self.val, 1);
        let barret = BARRETT.with(|v| *v.borrow());
        while exp > 0 {
            if exp & 1 == 1 {
                res = barret.reduce(res as u64 * val as u64);
            }
            val = barret.reduce(val as u64 * val as u64);
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
        let (mut s, mut ys) = (Self::modulo(), 0u32);
        let (mut t, mut yt) = (self.val, 1u32);
        while s % t != 0 {
            let tmp = s / t;
            let u = s - t * tmp;

            let (v, f) = yt.overflowing_mul(tmp);
            let yu = if f || v >= Self::modulo() {
                ys.wrapping_add(yt.wrapping_neg() * tmp)
            } else {
                ys.wrapping_sub(v)
            };

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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl std::fmt::Display for ArbitraryModint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl Add for ArbitraryModint {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        self.add_raw(rhs.val)
    }
}

impl AddAssign for ArbitraryModint {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for ArbitraryModint {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        self.sub_raw(rhs.val)
    }
}

impl SubAssign for ArbitraryModint {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Mul for ArbitraryModint {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        self.mul_raw(rhs.val)
    }
}

impl MulAssign for ArbitraryModint {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
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

impl Neg for ArbitraryModint {
    type Output = ArbitraryModint;
    fn neg(self) -> Self::Output {
        ArbitraryModint::zero() - self
    }
}

#[cfg(test)]
mod tests {
    use super::ArbitraryModint;

    #[test]
    fn dynamic_modint_test() {
        const A: u32 = 347384953;
        const B: u32 = 847362948;

        ArbitraryModint::set_modulo(998244353);
        let ma: ArbitraryModint = ArbitraryModint::new(A as u64);
        let mb: ArbitraryModint = ArbitraryModint::new(B as u64);

        let ma_inv = ma.inv();
        let mb_inv = mb.inv();

        assert!(ma_inv.val < ArbitraryModint::modulo());
        assert_eq!(
            ma.val as u64 * ma_inv.val as u64 % ArbitraryModint::modulo() as u64,
            1
        );
        assert_eq!(
            mb.val as u64 * mb_inv.val as u64 % ArbitraryModint::modulo() as u64,
            1
        );
        assert_eq!((ma + mb).val, 196503548);
        assert_eq!((ma - mb).val, 498266358);
        assert_eq!((ma * mb).val, 17486571);
        assert_eq!((ma / mb).val, 748159151);
        assert_eq!(ma.add_raw(B).val, 196503548);
        assert_eq!(ma.sub_raw(B).val, 498266358);
        assert_eq!(ma.mul_raw(B).val, 17486571);
        assert_eq!(ma.pow(B as u64).val, 860108694);
    }
}
