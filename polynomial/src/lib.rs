use std::ops::{Add, Div, Mul, Rem, Sub};

use convolution_simd::{convolution, dot, fft_cache::FftCache, intt, ntt};
use modint::{Modulo, MontgomeryModint};

#[derive(Debug, Clone)]
pub struct Polynomial<M: Modulo> {
    coefficients: Vec<MontgomeryModint<M>>,
}

impl<M: Modulo> Polynomial<M> {
    #[inline]
    pub fn deg(&self) -> usize { self.coefficients.len() }

    #[inline]
    pub fn scale(mut self, s: u32) -> Self {
        let s = MontgomeryModint::new(s);
        self.coefficients.iter_mut().for_each(|v| *v *= s);
        self
    }

    // reference: https://web.archive.org/web/20220903140644/https://opt-cp.com/fps-fast-algorithms/#toc4
    // reference: https://nyaannyaan.github.io/library/fps/formal-power-series.hpp
    // reference: https://judge.yosupo.jp/submission/68532
    pub fn inv(&self, deg: usize) -> Self {
        let mut g = vec![0; deg.next_power_of_two()];
        g[0] = self.coefficients[0].inv().val();
        let mut size = 1;
        while size < deg {
            let mut f = self.coefficients.iter().copied().take(2 * size).map(|v| v.val()).collect::<Vec<_>>();
            f.resize(2 * size, 0);
            let hg = if size >= 4 {
                let cache = FftCache::<MontgomeryModint<M>>::new((2 * size).trailing_zeros() as usize);

                let (f_ntt, g_ntt) = (ntt(f, &cache), ntt(g[0..2 * size].to_vec(), &cache));
                let fg = dot::<M>(f_ntt, g_ntt.clone());
                let mut h = intt(fg, &cache);
                h[..size].iter_mut().for_each(|h| *h = 0);
                let h_ntt = ntt(h, &cache);
                let hg = dot::<M>(h_ntt, g_ntt);
                intt(hg, &cache)
            } else {
                let mut h = convolution::<M>(f, g[0..2 * size].to_vec());
                h.resize(2 * size, 0);
                convolution::<M>(g[0..2 * size].to_vec(), h)
            };
            g[size..].iter_mut().zip(&hg[size..2 * size]).for_each(|(p, &v)| {
                let (r, f) = p.overflowing_sub(v);
                *p = if f { r.wrapping_add(M::MOD) } else { r };
            });
            size <<= 1;
        }

        Self {
            coefficients: g[0..deg].into_iter().map(|v| MontgomeryModint::new(*v)).collect(),
        }
    }

    #[inline]
    pub fn shrink(&mut self) {
        let garbage_cnt = self.coefficients.iter().rev().take_while(|&&v| v == MontgomeryModint::zero()).count();
        self.coefficients.resize(self.deg() - garbage_cnt, MontgomeryModint::zero());
    }

    #[inline]
    pub fn div_rem(self, rhs: Self) -> (Self, Self) {
        let q = self.clone() / rhs.clone();
        let mut r = self - rhs * q.clone();
        r.shrink();
        (q, r)
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
    fn sub(self, mut rhs: Self) -> Self::Output {
        rhs.coefficients.iter_mut().for_each(|v| *v = MontgomeryModint::zero() - *v);
        self + rhs
    }
}

impl<M: Modulo> Mul<Self> for Polynomial<M> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        let coefficients = convolution::<M>(self.coefficients.into_iter().map(|a| a.val()).collect(), rhs.coefficients.into_iter().map(|a| a.val()).collect());
        coefficients.into()
    }
}

impl<M: Modulo> Div<Self> for Polynomial<M> {
    type Output = Self;
    fn div(mut self, mut rhs: Self) -> Self::Output {
        let (n, m) = (self.deg(), rhs.deg());

        if n < m {
            return Self { coefficients: vec![] };
        }

        let k = n - m + 1;
        self.coefficients.reverse();
        rhs.coefficients.reverse();
        let rhs_inv = rhs.inv(k);
        let mut fg = self * rhs_inv;
        fg.coefficients.resize(k, MontgomeryModint::zero());
        fg.coefficients.reverse();
        fg.shrink();
        fg
    }
}

impl<M: Modulo> Rem<Self> for Polynomial<M> {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self::Output { self.div_rem(rhs).1 }
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
        let poly = Polynomial::<Mod998244353>::from(vec![5, 4, 3, 2, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![1, 2, 4, 8, 16]);

        let sub = (poly - poly2).coefficients.into_iter().map(|v| v.val()).collect::<Vec<_>>();
        assert_eq!(sub, vec![4, 2, 998244352, 998244347, 998244338]);
    }

    #[test]
    fn polynomial_mul_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![5, 4, 3, 2, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![1, 2, 4, 8, 16]);

        let mul = (poly * poly2).coefficients.into_iter().map(|v| v.val()).collect::<Vec<_>>();
        assert_eq!(mul, vec![5, 14, 31, 64, 129, 98, 68, 40, 16]);
    }

    #[test]
    fn polynomial_div_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![0, 0, 0, 0, 0, 0, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![998244352, 998244352, 1]);

        let div = (poly / poly2).coefficients.into_iter().map(|v| v.val()).collect::<Vec<_>>();
        assert_eq!(div, vec![5, 3, 2, 1, 1]);
    }

    #[test]
    fn polynomial_rem_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![0, 0, 0, 0, 0, 0, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![998244352, 998244352, 1]);

        let rem = (poly % poly2).coefficients.into_iter().map(|v| v.val()).collect::<Vec<_>>();
        assert_eq!(rem, vec![5, 8]);
    }

    #[test]
    fn polynomial_inverse_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![907649121, 290651129, 813718295, 770591820, 913049957, 587190944, 411145555, 899491439, 722412549, 182227749]);
        let inv = poly.inv(poly.deg()).coefficients.into_iter().map(|v| v.val()).collect::<Vec<_>>();

        assert_eq!(inv, vec![827228041, 288540417, 325694325, 929405258, 743378152, 901428113, 379325593, 870509167, 978731889, 911693879]);
    }

    #[test]
    fn multipoint_evaluation_test() {}
}
