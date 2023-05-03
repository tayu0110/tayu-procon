use convolution_simd::{fft_cache::FftCache, Nttable};
use montgomery_modint::{Modulo, MontgomeryModint, MontgomeryModintx8};
use std::ops::{Add, Div, Mul, Rem, Sub};

type Modint<M> = MontgomeryModint<M>;
type Modintx8<M> = MontgomeryModintx8<M>;

#[derive(Debug, Clone)]
pub struct Polynomial<M: Modulo> {
    coef: Vec<Modint<M>>,
}

impl<M: Modulo> Polynomial<M> {
    #[inline]
    pub fn deg(&self) -> usize { self.coef.len() }

    #[inline]
    pub fn scale(mut self, s: u32) -> Self {
        let s = Modint::new(s);
        self.coef.iter_mut().for_each(|v| *v *= s);
        self
    }

    #[inline]
    pub fn prefix(mut self, new_deg: usize) -> Self {
        self.resize(new_deg);
        self
    }

    #[inline]
    pub fn derivative(self) -> Self {
        let coef = self.coef[1..].into_iter().enumerate().map(|(i, p)| *p * Modint::raw(i as u32 + 1)).collect::<Vec<_>>();
        coef.into()
    }

    #[inline]
    fn naive_multiply(mut self, rhs: &Self) -> Self {
        let deg = self.deg();
        let new_deg = deg + rhs.deg() - 1;
        self.resize(new_deg);
        for i in (0..new_deg).rev() {
            let mut res = Modint::zero();
            for (j, &r) in rhs.coef.iter().enumerate().take_while(|&(j, _)| i >= j) {
                res += self.coef[i - j] * r;
            }
            self.coef[i] = res;
        }
        self
    }

    #[inline]
    fn mul_with_cache(mut self, rhs: &Self, cache: &FftCache<M>) -> Self {
        if self.deg().min(rhs.deg()) <= 32 {
            return self.naive_multiply(rhs);
        }
        let mut rhs = rhs.clone();
        let len = self.deg() + rhs.deg() - 1;
        let deg = len.next_power_of_two();
        self.resize(deg);
        rhs.resize(deg);
        self.coef.ntt_with_cache(&cache);
        rhs.coef.ntt_with_cache(&cache);
        let mut res = self.coef.dot(&rhs.coef);
        res.intt_with_cache(&cache);
        let mut res: Self = res.into();
        res.resize(len);
        res
    }

    // reference: https://web.archive.org/web/20220903140644/https://opt-cp.com/fps-fast-algorithms/#toc4
    // reference: https://nyaannyaan.github.io/library/fps/formal-power-series.hpp
    // reference: https://judge.yosupo.jp/submission/68532
    fn inv_with_cache(&self, deg: usize, cache: &FftCache<M>) -> Self {
        let mut g = vec![Modint::zero(); deg.next_power_of_two()];
        g[0] = self.coef[0].inv();
        let mut size = 1;
        while size < deg {
            let mut f = self.coef.iter().take(2 * size).cloned().collect::<Vec<_>>();
            f.resize(2 * size, Modint::zero());
            let hg = {
                let mut g_ntt = g[0..2 * size].to_vec();
                g_ntt.ntt_with_cache(&cache);
                f.ntt_with_cache(&cache);
                let mut fg = f.dot(&g_ntt);
                fg.intt_with_cache(&cache);
                fg[..size].iter_mut().for_each(|h| *h = Modint::zero());
                fg.ntt_with_cache(&cache);
                fg.dot_assign(&g_ntt);
                fg.intt_with_cache(&cache);
                fg
            };
            if size < 8 {
                g[size..].iter_mut().zip(hg[size..].iter().take(size)).for_each(|(p, &v)| *p -= v);
            } else {
                g[size..]
                    .chunks_exact_mut(8)
                    .zip(hg[size..].chunks_exact(8))
                    .for_each(|(p, v)| unsafe { (Modintx8::load_ptr(p.as_ptr()) - Modintx8::load_ptr(v.as_ptr())).store_ptr(p.as_mut_ptr()) });
            }
            size <<= 1;
        }

        g.resize(deg, Modint::zero());
        g.into()
    }

    #[inline]
    pub fn inv(&self, deg: usize) -> Self {
        let cache = Self::gen_caches();
        self.inv_with_cache(deg, &cache)
    }

    #[inline]
    fn reverse(&mut self) { self.coef.reverse() }

    #[inline]
    fn resize(&mut self, new_deg: usize) { self.coef.resize(new_deg, Modint::zero()); }

    #[inline]
    pub fn shrink(&mut self) {
        let garbage_cnt = self.coef.iter().rev().take_while(|&&v| v == Modint::zero()).count();
        self.coef.resize(self.deg() - garbage_cnt, Modint::zero());
    }

    #[inline]
    pub fn div_rem(self, rhs: Self) -> (Self, Self) {
        let q = self.clone() / rhs.clone();
        let mut r = self - rhs * q.clone();
        r.shrink();
        (q, r)
    }

    fn gen_subproduct_tree(xs: Vec<Modint<M>>) -> Vec<Polynomial<M>> {
        let len = xs.len();
        let m = len.next_power_of_two();
        let mut subproduct_tree = vec![Self { coef: vec![] }; m * 2];
        for i in 0..m {
            subproduct_tree[m + i] = Self {
                coef: vec![Modint::one(), -*xs.get(i).unwrap_or(&Modint::zero())],
            };
        }

        let cache = Self::gen_caches();
        for i in (1..m).rev() {
            let new_deg = (subproduct_tree[i << 1].deg() - 1) << 1;
            subproduct_tree[i << 1].resize(new_deg);
            subproduct_tree[(i << 1) | 1].resize(new_deg);
            subproduct_tree[i << 1].coef.ntt_with_cache(&cache);
            subproduct_tree[(i << 1) | 1].coef.ntt_with_cache(&cache);
            subproduct_tree[i] = Self {
                coef: subproduct_tree[i << 1].clone().coef.dot(&subproduct_tree[(i << 1) | 1].coef),
            };
            subproduct_tree[i].coef.intt_with_cache(&cache);
            let k = subproduct_tree[i].coef[0] - Modint::one();
            subproduct_tree[i].coef.push(k);
            subproduct_tree[i].coef[0] = Modint::one();
        }
        subproduct_tree
    }

    fn transposed_uptree(m: usize, mut subproduct_tree: Vec<Polynomial<M>>, cache: &FftCache<M>) -> Vec<Polynomial<M>> {
        for i in 1..m {
            let (a, b) = subproduct_tree.split_at_mut(i << 1);
            let n = a[i].deg() >> 1;
            a[i].coef.ntt_with_cache(&cache);
            for j in 0..2 {
                b[j].coef.dot_assign(&a[i].coef);
                b[j].coef.intt_with_cache(&cache);
                b[j].reverse();
                b[j].resize(n);
                b[j].reverse();
            }
            b.swap(0, 1);
        }
        subproduct_tree
    }

    // reference: https://specfun.inria.fr/bostan/publications/BoLeSc03.pdf
    // reference: https://judge.yosupo.jp/submission/127492
    pub fn multipoint_evaluation(mut self, xs: Vec<Modint<M>>) -> Vec<Modint<M>> {
        let len = xs.len();
        let m = len.next_power_of_two();
        let cache = Self::gen_caches();
        let mut subproduct_tree = Self::gen_subproduct_tree(xs);

        let n = self.deg();
        let alpha = subproduct_tree[1].inv_with_cache(n, &cache);
        self.reverse();
        let mut t = alpha * self;
        t.resize(n);
        t.reverse();
        t.resize(m);
        t.reverse();
        subproduct_tree[1] = t;

        let subproduct_tree = Self::transposed_uptree(m, subproduct_tree, &cache);
        subproduct_tree[m..m + len].into_iter().map(|v| *v.coef.get(0).unwrap_or(&Modint::zero())).collect()
    }

    pub fn interpolation(xs: Vec<Modint<M>>, fs: Vec<Modint<M>>) -> Self {
        let len = xs.len();
        assert_eq!(len, fs.len());
        let m = len.next_power_of_two();

        let cache = Self::gen_caches();
        let mut subproduct_tree = Self::gen_subproduct_tree(xs);
        let mut keep = subproduct_tree.clone();

        let mut p = subproduct_tree[1].clone().prefix(len + 1);
        p.reverse();
        let mut p = p.derivative();

        let n = p.deg();
        let alpha = subproduct_tree[1].inv_with_cache(n, &cache);
        p.reverse();
        let mut t = alpha * p;
        t.resize(n);
        t.reverse();
        t.resize(m);
        t.reverse();
        subproduct_tree[1] = t;

        let mut subproduct_tree = Self::transposed_uptree(m, subproduct_tree, &cache);

        for i in 1..m {
            let n = keep[i << 1].deg() >> 1;
            keep[i << 1].coef.intt_with_cache(&cache);
            keep[(i << 1) | 1].coef.intt_with_cache(&cache);
            keep[i << 1].resize(n + 1);
            keep[(i << 1) | 1].resize(n + 1);
            keep[i << 1].reverse();
            keep[(i << 1) | 1].reverse();
        }

        subproduct_tree[m..m + len]
            .iter_mut()
            .enumerate()
            .for_each(|(i, v)| *v = vec![fs[i] / *v.coef.get(0).unwrap_or(&Modint::zero())].into());
        subproduct_tree[m + len..].iter_mut().for_each(|v| *v = Self { coef: vec![] });
        for i in (1..m).rev() {
            let (r, l) = (subproduct_tree.pop().unwrap(), subproduct_tree.pop().unwrap());
            let (kr, kl) = (keep.pop().unwrap(), keep.pop().unwrap());
            if l.deg() == 0 && r.deg() == 0 {
                subproduct_tree[i] = l;
                keep[i].coef.clear();
                continue;
            }
            if r.deg() == 0 {
                subproduct_tree[i] = l;
                keep[i] = kl;
                continue;
            }
            if kl.deg() != kr.deg() {
                let new_deg = kl.deg() + kr.deg() - 1;
                keep[i].reverse();
                keep[i].resize(new_deg);
                keep[i].reverse();
            }
            subproduct_tree[i] = l.mul_with_cache(&kr, &cache) + r.mul_with_cache(&kl, &cache);
        }
        subproduct_tree.pop().unwrap()
    }

    #[inline(always)]
    fn gen_caches() -> FftCache<M> { FftCache::new() }
}

impl<M: Modulo> Add<Self> for Polynomial<M> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        let (mut l, mut r) = (self.coef, rhs.coef);
        if l.len() < r.len() {
            std::mem::swap(&mut l, &mut r);
        }

        l.iter_mut().zip(r.iter()).for_each(|(l, r)| *l += *r);
        Polynomial { coef: l }
    }
}

impl<M: Modulo> Sub<Self> for Polynomial<M> {
    type Output = Self;
    fn sub(self, mut rhs: Self) -> Self::Output {
        rhs.coef.iter_mut().for_each(|v| *v = -*v);
        self + rhs
    }
}

impl<M: Modulo> Mul<Self> for Polynomial<M> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        if self.deg() == 0 || rhs.deg() == 0 {
            return <Vec<Modint<M>> as Into<Polynomial<M>>>::into(vec![]);
        }
        if self.deg().min(rhs.deg()) <= 8 {
            return self.naive_multiply(&rhs);
        }
        let cache = FftCache::new();
        self.mul_with_cache(&rhs, &cache)
    }
}

impl<M: Modulo> Div<Self> for Polynomial<M> {
    type Output = Self;
    fn div(mut self, mut rhs: Self) -> Self::Output {
        let (n, m) = (self.deg(), rhs.deg());

        if n < m {
            return Self { coef: vec![] };
        }

        let k = n - m + 1;
        self.coef.reverse();
        rhs.coef.reverse();
        let rhs_inv = rhs.inv(k);
        let mut fg = self * rhs_inv;
        fg.resize(k);
        fg.coef.reverse();
        fg.shrink();
        fg
    }
}

impl<M: Modulo> Rem<Self> for Polynomial<M> {
    type Output = Self;
    fn rem(self, rhs: Self) -> Self::Output { self.div_rem(rhs).1 }
}

impl<M: Modulo> From<Vec<u32>> for Polynomial<M> {
    fn from(mut v: Vec<u32>) -> Self {
        let l = v.len() >> 3 << 3;
        v[..l].chunks_exact_mut(8).for_each(|v| {
            let w = unsafe { Modintx8::<M>::load_ptr(v.as_ptr() as _) * Modintx8::from_rawval(M::R2X8) };
            unsafe { w.store_ptr(v.as_mut_ptr() as _) }
        });
        v[l..].iter_mut().for_each(|v| *v = Modint::<M>::new(*v).val);
        Self { coef: unsafe { std::mem::transmute(v) } }
    }
}

impl<M: Modulo> From<Vec<Modint<M>>> for Polynomial<M> {
    fn from(v: Vec<Modint<M>>) -> Self { Self { coef: v } }
}

impl<M: Modulo> Into<Vec<u32>> for Polynomial<M> {
    fn into(mut self) -> Vec<u32> {
        let l = self.deg() >> 3 << 3;
        self.coef[..l].chunks_exact_mut(8).for_each(|v| {
            let w = Modintx8::load(&v);
            Modintx8::from_rawval(w.val()).store(v)
        });
        self.coef[l..].iter_mut().for_each(|v| *v = Modint::from_mont_expr(v.val()));
        unsafe { std::mem::transmute(self.coef) }
    }
}

impl<M: Modulo> Into<Vec<Modint<M>>> for Polynomial<M> {
    fn into(self) -> Vec<Modint<M>> { self.coef }
}

#[cfg(test)]
mod tests {
    use super::Polynomial;
    use montgomery_modint::Mod998244353;

    #[test]
    fn polynomial_add_test() {
        let coef = vec![5, 4, 3, 2, 1];
        let poly = Polynomial::<Mod998244353>::from(coef);

        let coef = vec![1, 2, 4, 8, 16];
        let poly2 = Polynomial::<Mod998244353>::from(coef);

        let add = (poly + poly2).coef.into_iter().map(|v| v.val()).collect::<Vec<_>>();
        assert_eq!(add, vec![6, 6, 7, 10, 17]);
    }

    #[test]
    fn polynomial_sub_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![5, 4, 3, 2, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![1, 2, 4, 8, 16]);

        let sub = (poly - poly2).coef.into_iter().map(|v| v.val()).collect::<Vec<_>>();
        assert_eq!(sub, vec![4, 2, 998244352, 998244347, 998244338]);
    }

    #[test]
    fn polynomial_mul_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![5, 4, 3, 2, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![1, 2, 4, 8, 16]);

        let mul = (poly * poly2).coef.into_iter().map(|v| v.val()).collect::<Vec<_>>();
        assert_eq!(mul, vec![5, 14, 31, 64, 129, 98, 68, 40, 16]);
    }

    #[test]
    fn polynomial_div_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![0, 0, 0, 0, 0, 0, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![998244352, 998244352, 1]);

        let div = (poly / poly2).coef.into_iter().map(|v| v.val()).collect::<Vec<_>>();
        assert_eq!(div, vec![5, 3, 2, 1, 1]);
    }

    #[test]
    fn polynomial_rem_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![0, 0, 0, 0, 0, 0, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![998244352, 998244352, 1]);

        let rem = (poly % poly2).coef.into_iter().map(|v| v.val()).collect::<Vec<_>>();
        assert_eq!(rem, vec![5, 8]);
    }

    #[test]
    fn polynomial_inverse_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![907649121, 290651129, 813718295, 770591820, 913049957, 587190944, 411145555, 899491439, 722412549, 182227749]);
        let inv = poly.inv(poly.deg()).coef.into_iter().map(|v| v.val()).collect::<Vec<_>>();

        assert_eq!(inv, vec![827228041, 288540417, 325694325, 929405258, 743378152, 901428113, 379325593, 870509167, 978731889, 911693879]);
    }

    #[test]
    fn multipoint_evaluation_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4]);
        let xs = vec![5.into(), 6.into(), 7.into(), 8.into(), 9.into()];
        let ys = poly.multipoint_evaluation(xs);

        assert_eq!(ys, vec![586.into(), 985.into(), 1534.into(), 2257.into(), 3178.into()]);
    }

    #[test]
    fn lagrange_interpolation_test() {
        let xs = vec![5.into(), 6.into(), 7.into(), 8.into(), 9.into()];
        let fs = vec![586.into(), 985.into(), 1534.into(), 2257.into(), 3178.into()];

        let res = Polynomial::<Mod998244353>::interpolation(xs, fs);
        assert_eq!(res.coef, vec![1.into(), 2.into(), 3.into(), 4.into(), 0.into()]);
    }
}
