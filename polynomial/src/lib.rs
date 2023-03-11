use std::ops::{Add, Div, Mul, Rem, Sub};

use convolution_simd::{fft_cache::FftCache, Nttable};
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

    #[inline]
    pub fn prefix(mut self, new_deg: usize) -> Self {
        self.resize(new_deg);
        self
    }

    #[inline]
    fn naive_multiply(mut self, mut rhs: Self) -> Self {
        if self.deg() < rhs.deg() {
            std::mem::swap(&mut self, &mut rhs);
        }
        let deg = self.deg();
        self.coefficients.resize(deg + rhs.deg() - 1, MontgomeryModint::zero());
        for i in (0..self.coefficients.len()).rev() {
            let mut res = MontgomeryModint::zero();
            for (j, &r) in rhs.coefficients.iter().enumerate().take_while(|&(j, _)| i >= j) {
                res += self.coefficients[i - j] * r;
            }
            self.coefficients[i] = res;
        }
        self
    }

    #[inline]
    fn mul_with_cache(mut self, mut rhs: Self, cache: &FftCache<MontgomeryModint<M>>) -> Self {
        let len = self.deg() + rhs.deg() - 1;
        let deg = len.next_power_of_two();
        assert_eq!(deg, cache.twiddle_factors().len() - 1);
        self.resize(deg);
        rhs.resize(deg);
        let (l, r) = (self.coefficients.ntt_with_cache(&cache), rhs.coefficients.ntt_with_cache(&cache));
        let mut res: Self = l.dot(&r).intt_with_cache(&cache).into();
        res.resize(len);
        res
    }

    // reference: https://web.archive.org/web/20220903140644/https://opt-cp.com/fps-fast-algorithms/#toc4
    // reference: https://nyaannyaan.github.io/library/fps/formal-power-series.hpp
    // reference: https://judge.yosupo.jp/submission/68532
    fn inv_with_cache(&self, deg: usize, cache: &Vec<FftCache<MontgomeryModint<M>>>) -> Self {
        let mut g = vec![MontgomeryModint::zero(); deg.next_power_of_two()];
        g[0] = self.coefficients[0].inv();
        let mut size = 1;
        while size < deg {
            let mut f = self.coefficients.iter().take(2 * size).cloned().collect::<Vec<_>>();
            f.resize(2 * size, MontgomeryModint::zero());
            let hg = if size >= 8 {
                let cache = &cache[(2 * size).trailing_zeros() as usize];
                let g_ntt = g[0..2 * size].to_vec().ntt_with_cache(&cache);
                let fg = f.ntt_with_cache(&cache).dot(&g_ntt);
                let mut h = fg.intt_with_cache(&cache);
                h[..size].iter_mut().for_each(|h| *h = MontgomeryModint::zero());
                h.ntt_with_cache(&cache).dot(&g_ntt).intt_with_cache(&cache)
            } else {
                let h = <Vec<MontgomeryModint<M>> as Into<Polynomial<M>>>::into(f) * g[0..size].to_vec().into();
                (h * g[0..size].to_vec().into()).into()
            };
            g[size..].iter_mut().zip(hg[size..].iter().take(size)).for_each(|(p, &v)| *p -= v);
            size <<= 1;
        }

        g.resize(deg, MontgomeryModint::zero());
        g.into()
    }

    #[inline]
    pub fn inv(&self, deg: usize) -> Self {
        let cache = Self::gen_caches(deg);
        self.inv_with_cache(deg, &cache)
    }

    #[inline]
    fn reverse(&mut self) { self.coefficients.reverse() }

    #[inline]
    fn resize(&mut self, new_deg: usize) { self.coefficients.resize(new_deg, MontgomeryModint::zero()); }

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

    #[inline]
    // middle_product(a, b) = sum_{j}{x^j * sum_{i}{a[i]c[i+j]}}
    //      Now, a <- reverse(a), a[i] move to a[n-1-i] (n = length(a))
    // convolution(reverse(a), c) = sum_{n-1+j}{a[n-1-i]c[i+j]}
    // middle_product(a, b) = sum_{j}{x^j * sum_{n-1+j}{a[n-1-i]c[i+j]}[n-1..]}
    //                      = sum_{j}{x^j * convolution(reverse(a), b)[n-1..]}
    fn middle_product(mut self, rhs: &Self, cache: &FftCache<MontgomeryModint<M>>) -> Self {
        let deg = self.deg();
        self.reverse();
        self.resize(rhs.deg());
        self.coefficients.ntt_with_cache(&cache).dot(&rhs.coefficients).intt_with_cache(&cache)[deg - 1..].to_vec().into()
    }

    fn gen_caches(size: usize) -> Vec<FftCache<MontgomeryModint<M>>> {
        let d = size.next_power_of_two().trailing_zeros() as usize;
        let mut t = Vec::with_capacity(d + 1);
        for i in 0..=d {
            t.push(FftCache::new(i));
        }
        t
    }

    pub fn multipoint_evaluation(mut self, xs: Vec<MontgomeryModint<M>>) -> Vec<MontgomeryModint<M>> {
        let len = xs.len();
        if len == 0 {
            return vec![];
        }

        let caches = Self::gen_caches(len.max(self.deg()).next_power_of_two() * 2);
        let mut subproduct_tree = vec![Self { coefficients: vec![] }; len * 2];
        for i in 0..len {
            subproduct_tree[len + i] = vec![-xs[i], MontgomeryModint::one()].into();
        }
        for i in (1..len).rev() {
            subproduct_tree[i] = if subproduct_tree[i * 2].deg() <= 8 {
                subproduct_tree[i * 2].clone() * subproduct_tree[i * 2 + 1].clone()
            } else {
                let ndeg = (subproduct_tree[i * 2].deg() + subproduct_tree[i * 2 + 1].deg() - 1).next_power_of_two();
                subproduct_tree[i * 2]
                    .clone()
                    .mul_with_cache(subproduct_tree[i * 2 + 1].clone(), &caches[ndeg.trailing_zeros() as usize])
            };
        }

        subproduct_tree.reverse();
        subproduct_tree.pop().unwrap();

        let mut uptree = vec![Self { coefficients: vec![] }; len * 2];
        let mut t = subproduct_tree.pop().unwrap();
        let deg = self.deg();
        t.reverse();
        self.resize(2 * deg.next_power_of_two());
        uptree[len * 2 - 1] = t.inv_with_cache(deg, &caches).middle_product(
            &self.coefficients.ntt_with_cache(&caches[(deg.next_power_of_two() * 2).trailing_zeros() as usize]).into(),
            &caches[(deg.next_power_of_two() * 2).trailing_zeros() as usize],
        );
        uptree[len * 2 - 1].resize(len);
        uptree[len * 2 - 1].reverse();

        for i in 1..len {
            let l = subproduct_tree.pop().unwrap();
            let r = subproduct_tree.pop().unwrap();
            let (dl, dr) = (l.deg(), r.deg());
            let mut u = uptree.pop().unwrap();
            let deg = (u.deg() + dl.max(dr)).next_power_of_two();
            u.resize(deg);
            let cache_index = deg.trailing_zeros() as usize;
            let nu = u.coefficients.ntt_with_cache(&caches[cache_index]).into();
            uptree[len * 2 - i * 2] = r.middle_product(&nu, &caches[cache_index]).prefix(dl);
            uptree[len * 2 - i * 2 - 1] = l.middle_product(&nu, &caches[cache_index]).prefix(dr);
        }

        uptree
            .into_iter()
            .rev()
            .take(len)
            .map(|v| if v.deg() == 0 { MontgomeryModint::zero() } else { v.coefficients[0] })
            .collect()
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
        rhs.coefficients.iter_mut().for_each(|v| *v = -*v);
        self + rhs
    }
}

impl<M: Modulo> Mul<Self> for Polynomial<M> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        if self.deg() == 0 || rhs.deg() == 0 {
            return <Vec<MontgomeryModint<M>> as Into<Polynomial<M>>>::into(vec![]);
        }
        if self.deg().min(rhs.deg()) <= 8 {
            return self.naive_multiply(rhs);
        }
        let deg = (self.deg() + rhs.deg() - 1).next_power_of_two();
        let cache = FftCache::new(deg.trailing_zeros() as usize);
        self.mul_with_cache(rhs, &cache)
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
        fg.resize(k);
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

impl<M: Modulo> From<Vec<MontgomeryModint<M>>> for Polynomial<M> {
    fn from(v: Vec<MontgomeryModint<M>>) -> Self { Self { coefficients: v } }
}

impl<M: Modulo> Into<Vec<u32>> for Polynomial<M> {
    fn into(self) -> Vec<u32> { self.coefficients.into_iter().map(|v| v.val()).collect() }
}

impl<M: Modulo> Into<Vec<MontgomeryModint<M>>> for Polynomial<M> {
    fn into(self) -> Vec<MontgomeryModint<M>> { self.coefficients }
}

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
    fn multipoint_evaluation_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4]);
        let xs = vec![5.into(), 6.into(), 7.into(), 8.into(), 9.into()];
        let ys = poly.multipoint_evaluation(xs);

        assert_eq!(ys, vec![586.into(), 985.into(), 1534.into(), 2257.into(), 3178.into()]);
    }
}
