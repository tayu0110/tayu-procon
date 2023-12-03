use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// ArbitraryMontgomeryModint
////////////////////////////////////////////////////////////////////////////////////////////////////////////
// t <- MR(T) = floor(T/R) - floor((TN' mod R)*N/R)
//  if t < 0 then return t + N else return t
//      T := a (0 <= T < NR)
//      N := MOD
//      N':= MOD_INV    NN' = 1 (mod R)
//      R := R
const fn montgomery_reduction(val: u64, modulo: u64, modulo_inv: u64) -> u64 {
    let (t, f) = (((val.wrapping_mul(modulo_inv) as u128).wrapping_mul(modulo as u128) >> 64)
        as u64)
        .overflowing_neg();
    t.wrapping_add(modulo * f as u64)
}

const fn montgomery_multiplication(lhs: u64, rhs: u64, modulo: u64, modulo_inv: u64) -> u64 {
    let a = lhs as u128 * rhs as u128;
    let (t, f) = ((a >> 64) as u64).overflowing_sub(
        (((a as u64).wrapping_mul(modulo_inv) as u128).wrapping_mul(modulo as u128) >> 64) as u64,
    );
    t.wrapping_add(modulo * f as u64)
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct ArbitraryMontgomeryModint {
    pub val: u64,
    modulo: u64,
    modulo_inv: u64,
    r: u64,
    r2: u64,
}

impl ArbitraryMontgomeryModint {
    #[inline]
    pub const fn new(val: u64, modulo: u64) -> Self {
        Self::raw(val % modulo, modulo)
    }

    pub const fn raw(val: u64, modulo: u64) -> Self {
        if modulo == 998244353 {
            let val = montgomery_multiplication(val, 299560064, modulo, 996491785301655553);
            return Self {
                val,
                modulo,
                modulo_inv: 996491785301655553,
                r: 932051910,
                r2: 299560064,
            };
        }
        let r = ((1u128 << 64) % modulo as u128) as u64;
        let r2 = ((modulo as u128).wrapping_neg() % modulo as u128) as u64;
        let modulo_inv = {
            let inv = modulo.wrapping_mul(2u64.wrapping_sub(modulo.wrapping_mul(modulo)));
            let inv = inv.wrapping_mul(2u64.wrapping_sub(modulo.wrapping_mul(inv)));
            let inv = inv.wrapping_mul(2u64.wrapping_sub(modulo.wrapping_mul(inv)));
            let inv = inv.wrapping_mul(2u64.wrapping_sub(modulo.wrapping_mul(inv)));
            inv.wrapping_mul(2u64.wrapping_sub(modulo.wrapping_mul(inv)))
        };
        let val = montgomery_multiplication(val, r2, modulo, modulo_inv);
        Self { val, modulo, modulo_inv, r, r2 }
    }

    #[inline]
    const fn from_raw_parts_unchecked(
        val: u64,
        modulo: u64,
        modulo_inv: u64,
        r: u64,
        r2: u64,
    ) -> Self {
        Self { val, modulo, modulo_inv, r, r2 }
    }

    #[inline]
    pub const fn from_same_mod(val: u64, from: Self) -> Self {
        Self::from_same_mod_unchecked(val % from.modulo, from)
    }

    #[inline]
    pub const fn from_same_mod_unchecked(val: u64, from: Self) -> Self {
        let val = montgomery_multiplication(val, from.r2, from.modulo, from.modulo_inv);
        Self::from_raw_parts_unchecked(val, from.modulo, from.modulo_inv, from.r, from.r2)
    }

    #[inline]
    pub const fn val(&self) -> u64 {
        montgomery_reduction(self.val, self.modulo, self.modulo_inv)
    }

    #[inline]
    pub const fn rawval(&self) -> u64 {
        self.val
    }

    #[inline]
    pub const fn one(&self) -> Self {
        Self {
            val: self.r,
            modulo: self.modulo,
            modulo_inv: self.modulo_inv,
            r: self.r,
            r2: self.r2,
        }
    }

    #[inline]
    pub const fn zero(&self) -> Self {
        Self {
            val: 0,
            modulo: self.modulo,
            modulo_inv: self.modulo_inv,
            r: self.r,
            r2: self.r2,
        }
    }

    pub fn pow(&self, mut n: u64) -> Self {
        let mut val = self.val;
        let mut res = self.r;
        while n != 0 {
            if n & 1 != 0 {
                res = montgomery_multiplication(res, val, self.modulo, self.modulo_inv);
            }
            val = montgomery_multiplication(val, val, self.modulo, self.modulo_inv);
            n >>= 1;
        }
        Self {
            val: res,
            modulo: self.modulo,
            modulo_inv: self.modulo_inv,
            r: self.r,
            r2: self.r2,
        }
    }

    #[inline]
    pub fn inv(&self) -> Self {
        self.pow(self.modulo - 2)
    }
}

impl Add for ArbitraryMontgomeryModint {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        let (t, fa) = self.val.overflowing_add(rhs.val);
        let (u, fs) = t.overflowing_sub(self.modulo);
        Self {
            val: if fa || !fs { u } else { t },
            modulo: self.modulo,
            modulo_inv: self.modulo_inv,
            r: self.r,
            r2: self.r2,
        }
    }
}

impl Sub for ArbitraryMontgomeryModint {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        let (val, f) = self.val.overflowing_sub(rhs.val);
        Self {
            val: if f { val.wrapping_add(self.modulo) } else { val },
            modulo: self.modulo,
            modulo_inv: self.modulo_inv,
            r: self.r,
            r2: self.r2,
        }
    }
}

impl Mul for ArbitraryMontgomeryModint {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            val: montgomery_multiplication(self.val, rhs.val, self.modulo, self.modulo_inv),
            modulo: self.modulo,
            modulo_inv: self.modulo_inv,
            r: self.r,
            r2: self.r2,
        }
    }
}

impl Div for ArbitraryMontgomeryModint {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inv()
    }
}

impl AddAssign for ArbitraryMontgomeryModint {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl SubAssign for ArbitraryMontgomeryModint {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl MulAssign for ArbitraryMontgomeryModint {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl DivAssign for ArbitraryMontgomeryModint {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl std::fmt::Debug for ArbitraryMontgomeryModint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val())
    }
}

impl std::fmt::Display for ArbitraryMontgomeryModint {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val())
    }
}

#[cfg(test)]
mod tests {
    use super::ArbitraryMontgomeryModint;

    #[test]
    fn dynamic_montgomery_modint_test() {
        type Modint = ArbitraryMontgomeryModint;

        const MOD: u64 = 998244353;
        const A: u64 = 347384953;
        const B: u64 = 847362948;

        const MA: Modint = Modint::new(A, MOD);
        const MB: Modint = Modint::new(B, MOD);
        assert_eq!(MA.val(), A);
        assert_eq!(MB.val(), B);

        assert_eq!(MA.zero().val(), 0);
        assert_eq!(MA.one().val(), 1);

        assert_eq!((MA + MB).val(), 196503548);
        assert_eq!((MA - MB).val(), 498266358);
        assert_eq!(
            (MA * MB).val(),
            (A as u128 * B as u128 % MOD as u128) as u64
        );
        assert_eq!(MA.pow(B).val(), 860108694);
        assert_eq!((MA / MB).val(), 748159151);
    }
}
