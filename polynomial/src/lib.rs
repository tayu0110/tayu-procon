use std::ops::{Add, Mul, Sub};

use convolution_simd::convolution;
use modint::{Modulo, MontgomeryModint};

#[derive(Debug, Clone)]
pub struct Polynomial<M: Modulo> {
    coefficients: Vec<MontgomeryModint<M>>,
}

impl<M: Modulo> Polynomial<M> {
    pub fn deg(&self) -> usize { self.coefficients.len() }

    pub fn scale(mut self, s: u32) -> Self {
        let s = MontgomeryModint::new(s);
        self.coefficients.iter_mut().for_each(|v| *v *= s);
        Self { coefficients: self.coefficients }
    }

    pub fn inv(&self) -> Self {
        let deg = self.deg();
        let mut g = Self { coefficients: vec![self.coefficients[0].inv()] };
        let mut size = 1;
        while size < deg {
            let mut ng = g.clone().scale(2);
            let t = self.clone() * g.clone() * g;
            ng = ng - t;
            g = ng;
            size <<= 1;
            g.coefficients.resize(size, MontgomeryModint::zero());
        }

        g.coefficients.resize(deg, MontgomeryModint::zero());
        g
    }
}

impl<M: Modulo> Add<Self> for Polynomial<M> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        let (mut l, mut r) = (self.coefficients, rhs.coefficients);
        if l.len() < r.len() {
            std::mem::swap(&mut l, &mut r);
        }

        l.iter_mut().zip(r.iter()).for_each(|(l, r)| *l += *r);
        Polynomial { coefficients: l }
    }
}

impl<M: Modulo> Sub<Self> for Polynomial<M> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        let (mut l, mut r) = (self.coefficients, rhs.coefficients);
        r.iter_mut().for_each(|v| *v = MontgomeryModint::zero() - *v);
        if l.len() < r.len() {
            std::mem::swap(&mut l, &mut r);
        }

        l.iter_mut().zip(r.iter()).for_each(|(l, r)| *l += *r);
        Polynomial { coefficients: l }
    }
}

impl<M: Modulo> Mul<Self> for Polynomial<M> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let coefficients = convolution::<M>(self.coefficients.into_iter().map(|a| a.val()).collect(), rhs.coefficients.into_iter().map(|a| a.val()).collect());
        Polynomial {
            coefficients: coefficients.into_iter().map(|a| MontgomeryModint::raw(a)).collect(),
        }
    }
}

impl<M: Modulo> From<Vec<u32>> for Polynomial<M> {
    fn from(v: Vec<u32>) -> Self {
        Self {
            coefficients: v.into_iter().map(|v| MontgomeryModint::new(v)).collect(),
        }
    }
}

impl<M: Modulo> Into<Vec<u32>> for Polynomial<M> {
    fn into(self) -> Vec<u32> { self.coefficients.into_iter().map(|v| v.val()).collect() }
}

pub fn multipoint_evaluation() {}

#[cfg(test)]
mod tests {
    use super::Polynomial;
    use modint::Mod998244353;

    #[test]
    fn polynomial_add_test() {
        let coef = vec![5, 4, 3, 2, 1];
        let poly = Polynomial::<Mod998244353>::from(coef);

        let coef = vec![1, 2, 4, 8, 16];
        let poly2 = Polynomial::<Mod998244353>::from(coef);

        let add = (poly + poly2).coefficients.into_iter().map(|v| v.val()).collect::<Vec<_>>();
        assert_eq!(add, vec![6, 6, 7, 10, 17]);
    }

    #[test]
    fn polynomial_sub_test() {
        let coef = vec![5, 4, 3, 2, 1];
        let poly = Polynomial::<Mod998244353>::from(coef);

        let coef = vec![1, 2, 4, 8, 16];
        let poly2 = Polynomial::<Mod998244353>::from(coef);

        let sub = (poly - poly2).coefficients.into_iter().map(|v| v.val()).collect::<Vec<_>>();
        assert_eq!(sub, vec![4, 2, 998244352, 998244347, 998244338]);
    }

    #[test]
    fn polynomial_mul_test() {
        let coef = vec![5, 4, 3, 2, 1];
        let poly = Polynomial::<Mod998244353>::from(coef);

        let coef = vec![1, 2, 4, 8, 16];
        let poly2 = Polynomial::<Mod998244353>::from(coef);

        let mul = (poly * poly2).coefficients.into_iter().map(|v| v.val()).collect::<Vec<_>>();
        assert_eq!(mul, vec![5, 14, 31, 64, 129, 98, 68, 40, 16]);
    }

    #[test]
    fn polynomial_inverse_test() {
        let coef = vec![5, 4, 3, 2, 1];
        let poly = Polynomial::<Mod998244353>::from(coef);
        let inv = poly.inv().coefficients.into_iter().map(|v| v.val()).collect::<Vec<_>>();

        assert_eq!(inv, vec![598946612, 718735934, 862483121, 635682004, 163871793]);
    }

    #[test]
    fn multipoint_evaluation_test() {}
}
