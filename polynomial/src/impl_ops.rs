use std::ops::{
    Add, AddAssign, Div, Index, IndexMut, Mul, MulAssign, Rem, Shl, ShlAssign, Shr, ShrAssign, Sub,
    SubAssign,
};

use montgomery_modint::{Modulo, MontgomeryModint};

use crate::Polynomial;

type Modint<M> = MontgomeryModint<M>;

impl<M: Modulo> Add<Self> for Polynomial<M> {
    type Output = Self;
    fn add(mut self, rhs: Self) -> Self::Output {
        self += rhs;
        self
    }
}

impl<M: Modulo> AddAssign for Polynomial<M> {
    fn add_assign(&mut self, mut rhs: Self) {
        if self.deg() < rhs.deg() {
            std::mem::swap(&mut self.coef, &mut rhs.coef);
        }

        self.coef
            .iter_mut()
            .zip(rhs.coef.iter())
            .for_each(|(l, r)| *l += *r);
    }
}

impl<M: Modulo> Sub<Self> for Polynomial<M> {
    type Output = Self;
    fn sub(mut self, rhs: Self) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<M: Modulo> SubAssign for Polynomial<M> {
    fn sub_assign(&mut self, mut rhs: Self) {
        if self.deg() >= rhs.deg() {
            self.coef
                .iter_mut()
                .zip(rhs.coef)
                .for_each(|(s, r)| *s -= r);
        } else {
            let d = self.deg();
            std::mem::swap(&mut self.coef, &mut rhs.coef);
            self.coef
                .iter_mut()
                .zip(rhs.coef)
                .for_each(|(s, r)| *s = r - *s);
            self.coef.iter_mut().skip(d).for_each(|s| *s = -*s);
        }
    }
}

impl<M: Modulo> Mul<Self> for Polynomial<M> {
    type Output = Self;
    fn mul(mut self, rhs: Self) -> Self::Output {
        self *= rhs;
        self
    }
}

impl<M: Modulo> MulAssign for Polynomial<M> {
    fn mul_assign(&mut self, rhs: Self) {
        if self.deg() == 0 {
            return;
        }
        if rhs.deg() == 0 {
            self.coef.clear();
            return;
        }
        *self = rhs.multiply(self);
    }
}

impl<M: Modulo> Div<Self> for Polynomial<M> {
    type Output = Self;
    fn div(mut self, mut rhs: Self) -> Self::Output {
        let (n, m) = (self.deg(), rhs.deg());

        if n < m {
            return Self::empty();
        }

        let k = n - m + 1;
        self.reverse();
        rhs.reverse();
        let rhs_inv = rhs.inv(k);
        let mut fg = self * rhs_inv;
        fg.resize(k);
        fg.reverse();
        fg.shrink();
        fg
    }
}

impl<M: Modulo> Rem<Self> for Polynomial<M> {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self::Output {
        self.div_rem(rhs).1
    }
}

impl<M: Modulo> Shl<usize> for &Polynomial<M> {
    type Output = Polynomial<M>;
    fn shl(self, rhs: usize) -> Self::Output {
        let mut coef = vec![Modint::zero(); rhs];
        coef.extend(&self.coef);
        Polynomial { coef }
    }
}

impl<M: Modulo> Shl<u32> for &Polynomial<M> {
    type Output = Polynomial<M>;
    fn shl(self, rhs: u32) -> Self::Output {
        self << (rhs as usize)
    }
}

impl<M: Modulo> Shl<usize> for Polynomial<M> {
    type Output = Polynomial<M>;
    fn shl(mut self, rhs: usize) -> Self::Output {
        self <<= rhs;
        self
    }
}

impl<M: Modulo> Shl<u32> for Polynomial<M> {
    type Output = Self;
    fn shl(self, rhs: u32) -> Self::Output {
        self << (rhs as usize)
    }
}

impl<M: Modulo> ShlAssign<usize> for Polynomial<M> {
    fn shl_assign(&mut self, rhs: usize) {
        if rhs > 0 {
            let mut coef = vec![Modint::zero(); self.deg() + rhs];
            coef[rhs..].copy_from_slice(&self.coef);
            self.coef = coef;
        }
    }
}

impl<M: Modulo> ShlAssign<u32> for Polynomial<M> {
    fn shl_assign(&mut self, rhs: u32) {
        *self <<= rhs as usize;
    }
}

impl<M: Modulo> ShlAssign<u64> for Polynomial<M> {
    fn shl_assign(&mut self, rhs: u64) {
        *self <<= rhs as usize;
    }
}

impl<M: Modulo> Shr<usize> for &Polynomial<M> {
    type Output = Polynomial<M>;
    fn shr(self, rhs: usize) -> Self::Output {
        if rhs >= self.deg() {
            return Polynomial::zero();
        }
        Polynomial { coef: self.coef[rhs..].to_vec() }
    }
}

impl<M: Modulo> Shr<u32> for &Polynomial<M> {
    type Output = Polynomial<M>;
    fn shr(self, rhs: u32) -> Self::Output {
        self >> (rhs as usize)
    }
}

impl<M: Modulo> Shr<usize> for Polynomial<M> {
    type Output = Self;
    fn shr(mut self, rhs: usize) -> Self::Output {
        self >>= rhs;
        self
    }
}

impl<M: Modulo> Shr<u32> for Polynomial<M> {
    type Output = Self;
    fn shr(self, rhs: u32) -> Self::Output {
        self >> (rhs as usize)
    }
}

impl<M: Modulo> ShrAssign<usize> for Polynomial<M> {
    fn shr_assign(&mut self, rhs: usize) {
        if rhs >= self.deg() {
            self.coef.clear();
        } else {
            self.reverse();
            self.resize(self.deg() - rhs);
            self.reverse();
        }
    }
}

impl<M: Modulo> ShrAssign<u32> for Polynomial<M> {
    fn shr_assign(&mut self, rhs: u32) {
        *self >>= rhs as usize;
    }
}

impl<M: Modulo> ShrAssign<u64> for Polynomial<M> {
    fn shr_assign(&mut self, rhs: u64) {
        *self >>= rhs as usize;
    }
}

impl<M: Modulo> Index<usize> for Polynomial<M> {
    type Output = Modint<M>;
    fn index(&self, index: usize) -> &Self::Output {
        &self.coef[index]
    }
}

impl<M: Modulo> IndexMut<usize> for Polynomial<M> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.coef[index]
    }
}
