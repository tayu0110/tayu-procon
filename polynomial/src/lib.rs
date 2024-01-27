use std::{
    mem::transmute,
    ops::{Add, AddAssign, Div, Index, IndexMut, Mul, MulAssign, Rem, Shl, Shr, Sub, SubAssign},
};

use convolution::hadamard;
use montgomery_modint::{Modulo, MontgomeryModint, MontgomeryModintx8};
use number_theoretic_transform::NumberTheoreticTransform;
use zero_one::{One, Zero};

type Modint<M> = MontgomeryModint<M>;
type Modintx8<M> = MontgomeryModintx8<M>;

#[derive(Debug, Clone)]
pub struct Polynomial<M: Modulo> {
    coef: Vec<Modint<M>>,
}

impl<M: Modulo> Polynomial<M> {
    #[inline]
    pub fn empty() -> Self {
        Self { coef: vec![] }
    }

    #[inline]
    pub fn deg(&self) -> usize {
        self.coef.len()
    }

    #[inline]
    pub fn scale(mut self, s: Modint<M>) -> Self {
        let sv = Modintx8::splat(s);
        let mut it = self.coef.chunks_exact_mut(8);
        for v in it.by_ref() {
            unsafe {
                let mv = Modintx8::load(v.as_ptr());
                (mv * sv).store(v.as_mut_ptr());
            }
        }
        it.into_remainder().iter_mut().for_each(|v| *v *= s);
        self
    }

    #[inline]
    pub fn prefix(&self, new_deg: usize) -> Self {
        let mut res = self.coef.iter().copied().take(new_deg).collect::<Vec<_>>();
        res.resize(new_deg, Modint::zero());
        Self { coef: res }
    }

    #[inline]
    pub fn derivative(&self) -> Self {
        self.coef
            .iter()
            .copied()
            .enumerate()
            .skip(1)
            .map(|(i, p)| p * Modint::new(i as u32))
            .collect::<Vec<_>>()
            .into()
    }

    pub fn integral(&self) -> Self {
        self._integral(Self::gen_inverse_table(self.deg()))
    }

    fn _integral(&self, table: Vec<Modint<M>>) -> Self {
        if self.deg() == 0 {
            Self::zero()
        } else if self.deg() == 1 {
            let mut res = Self::from(vec![Modint::zero(), self[0]]);
            res.shrink();
            res
        } else {
            let mut coef = table;
            coef.iter_mut()
                .skip(1)
                .zip(&self.coef)
                .for_each(|(n, &c)| *n *= c);
            Self { coef }
        }
    }

    // https://37zigen.com/linear-sieve/#i-4
    fn gen_inverse_table(deg: usize) -> Vec<Modint<M>> {
        let mut inv = vec![u32::MAX; deg + 1];
        {
            let mut primes = vec![];
            for i in 2..deg + 1 {
                if inv[i] == u32::MAX {
                    inv[i] = i as u32;
                    primes.push(i as u32);
                }
                for &p in &primes {
                    if p * i as u32 > deg as u32 || p > inv[i] {
                        break;
                    }
                    inv[p as usize * i] = p;
                }
            }
        }

        inv[0] = 0;
        inv[1] = Modint::<M>::one().rawval();
        for i in 2..deg + 1 {
            if inv[i] == i as u32 {
                inv[i] = Modint::<M>::new(i as u32).inv().rawval();
            } else {
                let (p, q) = (inv[i], i as u32 / inv[i]);
                inv[i] = (Modint::<M>::from_rawval(inv[p as usize])
                    * Modint::from_rawval(inv[q as usize]))
                .rawval();
            }

            debug_assert_eq!(
                Modint::<M>::new(i as u32) * Modint::from_rawval(inv[i] as u32),
                Modint::one()
            );
        }
        unsafe { transmute(inv) }
    }

    // This version assumes that `rhs.deg()` is significantly smaller than `self.deg()`.
    // If `rhs.deg()` is larger, performance will be significantly degraded and will need to be corrected in the future.
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
    fn multiply(mut self, rhs: &Self) -> Self {
        if rhs.deg() <= 8 {
            return self.naive_multiply(rhs);
        }
        let mut rhs = rhs.clone();
        let len = self.deg() + rhs.deg() - 1;
        let deg = len.next_power_of_two();
        self.resize(deg);
        rhs.resize(deg);
        self.coef.ntt();
        rhs.coef.ntt();
        hadamard(&mut self.coef, &rhs.coef);
        self.coef.intt();
        self.resize(len);
        self
    }

    fn doubling_step_for_inv(&self, mut g: Self) -> Self {
        debug_assert_eq!(1 << g.deg().trailing_zeros(), g.deg());
        // `g` must be the inverse of `self` on mod `g.deg()`
        debug_assert_eq!(
            {
                let mut g = self.clone().multiply(&g).prefix(g.deg());
                g.shrink();
                g.coef
            },
            Self::one().coef
        );
        let size = g.deg();
        let mut f = self.prefix(size << 1);
        g.resize(size << 1);
        let hg = {
            let mut g_ntt = g.prefix(size << 1);
            g_ntt.coef.ntt();
            f.coef.ntt();
            hadamard(&mut f.coef, &g_ntt.coef);
            f.coef.intt();
            f.coef[..size].fill(Modint::zero());
            f.coef.ntt();
            hadamard(&mut f.coef, &g_ntt.coef);
            f.coef.intt();
            f
        };
        let mut git = g.coef[size..2 * size].chunks_exact_mut(8);
        let mut hgit = hg.coef[size..].chunks_exact(8);
        for (p, v) in git.by_ref().zip(hgit.by_ref()) {
            unsafe {
                (Modintx8::load(p.as_ptr()) - Modintx8::load(v.as_ptr())).store(p.as_mut_ptr());
            }
        }
        git.into_remainder()
            .iter_mut()
            .zip(hgit.remainder())
            .for_each(|(p, v)| *p -= *v);
        g
    }

    // reference: https://web.archive.org/web/20220903140644/https://opt-cp.com/fps-fast-algorithms/#toc4
    // reference: https://nyaannyaan.github.io/library/fps/formal-power-series.hpp
    // reference: https://judge.yosupo.jp/submission/68532
    pub fn inv(&self, deg: usize) -> Self {
        let mut res = Self::one();
        res[0] = self[0].inv();
        res.coef.reserve(deg);
        let mut size = 1;
        while size < deg {
            res = self.doubling_step_for_inv(res);
            size <<= 1;
        }
        res.prefix(deg)
    }

    #[inline]
    fn reverse(&mut self) {
        self.coef.reverse()
    }

    #[inline]
    fn resize(&mut self, new_deg: usize) {
        self.coef.resize(new_deg, Modint::zero());
    }

    #[inline]
    pub fn shrink(&mut self) {
        let garbage_cnt = self
            .coef
            .iter()
            .rev()
            .take_while(|&&v| v == Modint::zero())
            .count();
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

        for i in (1..m).rev() {
            let new_deg = (subproduct_tree[i << 1].deg() - 1) << 1;
            subproduct_tree[i << 1].resize(new_deg);
            subproduct_tree[(i << 1) | 1].resize(new_deg);
            subproduct_tree[i << 1].coef.ntt();
            subproduct_tree[(i << 1) | 1].coef.ntt();
            subproduct_tree[i] = Self {
                coef: {
                    let mut coef = subproduct_tree[i << 1].clone().coef;
                    hadamard(&mut coef, &subproduct_tree[(i << 1) | 1].coef);
                    coef
                },
            };
            subproduct_tree[i].coef.intt();
            let k = subproduct_tree[i].coef[0] - Modint::one();
            subproduct_tree[i].coef.push(k);
            subproduct_tree[i].coef[0] = Modint::one();
        }
        subproduct_tree
    }

    fn transposed_uptree(m: usize, mut subproduct_tree: Vec<Polynomial<M>>) -> Vec<Polynomial<M>> {
        for i in 1..m {
            let (a, b) = subproduct_tree.split_at_mut(i << 1);
            let n = a[i].deg() >> 1;
            a[i].coef.ntt();
            for b in b.iter_mut().take(2) {
                hadamard(&mut b.coef, &a[i].coef);
                b.coef.intt();
                b.reverse();
                b.resize(n);
                b.reverse();
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
        let mut subproduct_tree = Self::gen_subproduct_tree(xs);

        let n = self.deg();
        let alpha = subproduct_tree[1].inv(n);
        self.reverse();
        let mut t = alpha * self;
        t.resize(n);
        t.reverse();
        t.resize(m);
        t.reverse();
        subproduct_tree[1] = t;

        let subproduct_tree = Self::transposed_uptree(m, subproduct_tree);
        subproduct_tree[m..m + len]
            .iter()
            .map(|v| *v.coef.first().unwrap_or(&Modint::zero()))
            .collect()
    }

    pub fn interpolation(xs: Vec<Modint<M>>, fs: Vec<Modint<M>>) -> Self {
        let len = xs.len();
        assert_eq!(len, fs.len());
        let m = len.next_power_of_two();

        let mut subproduct_tree = Self::gen_subproduct_tree(xs);
        let mut keep = subproduct_tree.clone();

        let mut p = subproduct_tree[1].clone().prefix(len + 1);
        p.reverse();
        let mut p = p.derivative();

        let n = p.deg();
        let alpha = subproduct_tree[1].inv(n);
        p.reverse();
        let mut t = alpha * p;
        t.resize(n);
        t.reverse();
        t.resize(m);
        t.reverse();
        subproduct_tree[1] = t;

        let mut subproduct_tree = Self::transposed_uptree(m, subproduct_tree);

        for i in 1..m {
            let n = keep[i << 1].deg() >> 1;
            keep[i << 1].coef.intt();
            keep[i << 1].resize(n + 1);
            keep[i << 1].reverse();
            keep[(i << 1) | 1].coef.intt();
            keep[(i << 1) | 1].resize(n + 1);
            keep[(i << 1) | 1].reverse();
        }

        subproduct_tree[m..m + len]
            .iter_mut()
            .enumerate()
            .for_each(|(i, v)| {
                *v = vec![fs[i] / *v.coef.first().unwrap_or(&Modint::zero())].into()
            });
        subproduct_tree[m + len..].fill(Self::empty());
        for i in (1..m).rev() {
            let (r, l) = (
                subproduct_tree.pop().unwrap(),
                subproduct_tree.pop().unwrap(),
            );
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
            subproduct_tree[i] = l * kr + r * kl;
        }
        subproduct_tree.pop().unwrap()
    }

    pub fn sqrt(&self, deg: usize) -> Option<Self> {
        if self.deg() == 0 {
            return Some(Self::zero());
        }

        if self[0] == Modint::zero() {
            let Some(pos) = self.coef.iter().position(|c| c != &Modint::zero()) else {
                return Some(Self::zero().prefix(deg));
            };
            if pos & 1 != 0 {
                return None;
            }
            if deg <= pos >> 1 {
                return Some(Self::zero().prefix(deg));
            }

            return Some((self >> pos).sqrt(deg - (pos >> 1))? << (pos >> 1));
        }

        let mut now = 1;
        let sqrt = self[0].sqrt()?;
        let inv2 = Modint::new(2).inv();
        let mut res = Self::from(vec![sqrt]);
        while now < deg {
            now <<= 1;
            res += res.inv(now).multiply(
                &self
                    .coef
                    .iter()
                    .copied()
                    .take(now)
                    .collect::<Vec<_>>()
                    .into(),
            );
            res = res.scale(inv2);
        }
        Some(res.prefix(deg))
    }

    pub fn log(&self, deg: usize) -> Option<Self> {
        (self.deg() >= 1 && self[0] == Modint::one()).then_some(
            (self.derivative() * self.inv(deg))
                ._integral(Self::gen_inverse_table(deg))
                .prefix(deg),
        )
    }

    // reference: https://judge.yosupo.jp/submission/70211
    pub fn exp(&self, deg: usize) -> Option<Self> {
        if self.deg() >= 1 && self[0] != Modint::zero() {
            return None;
        }
        if self.deg() == 0 {
            return Some(Self::one());
        }

        let mut written = 0;
        let mut now = 1;
        let mut res = Self::one();
        let mut inv = Self::one();
        let mut table = Self::gen_inverse_table(deg.next_power_of_two());
        while now < deg {
            let mut f = res.prefix(now << 1);
            let mut g = inv.prefix(now << 1);
            f.coef.ntt();
            g.coef.ntt();

            let mut w = self.prefix(now).derivative() << 1u32;
            table[written..now]
                .iter_mut()
                .zip(&w.coef[written..now])
                .for_each(|(s, t)| *s *= *t);
            written = now;

            w.coef.ntt();
            hadamard(&mut w.coef, &f.prefix(now).coef);
            w.coef.intt();
            w = (res.derivative() << 1u32) - w;

            w.resize(now << 1);
            w.coef.ntt();
            hadamard(&mut w.coef, &g.coef);
            w.coef.intt();

            let mut z = self.prefix(now << 1) - table[..now].into();
            z.coef[now..]
                .iter_mut()
                .zip(table[now..].iter().zip(w.coef).map(|(s, t)| *s * t))
                .for_each(|(s, t)| *s -= t);
            z.coef.ntt();
            hadamard(&mut z.coef, &f.coef);
            z.coef.intt();
            res.coef.extend(&z.coef[now..]);

            now <<= 1;
            if now < deg {
                inv = res.doubling_step_for_inv(inv);
            }
        }
        Some(res.prefix(deg))
    }

    pub fn pow(&self, n: u64, deg: usize) -> Self {
        if n == 0 {
            return Self::one().prefix(deg);
        }
        if self.deg() == 0 {
            return Self::zero().prefix(deg);
        }

        if self[0] != Modint::one() {
            let Some(pos) = self.coef.iter().position(|c| *c != Modint::zero()) else {
                return Self::zero().prefix(deg);
            };

            if deg as u128 <= pos as u128 * n as u128 {
                return Self::zero().prefix(deg);
            }

            let mut f = self >> pos;
            let f0 = f[0];
            f = f.scale(f0.inv());

            return f.pow(n, deg - pos * n as usize).scale(f0.pow(n)) << (pos * n as usize);
        }

        self.log(deg)
            .unwrap()
            .scale(Modint::from(n))
            .exp(deg)
            .unwrap()
    }
}

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
    fn mul_assign(&mut self, mut rhs: Self) {
        if self.deg() == 0 {
            return;
        }
        if rhs.deg() == 0 {
            self.coef.clear();
            return;
        }
        // Due to the constraints of `naive_multiply()`, the right side must always be smaller.
        if self.deg() > rhs.deg() {
            std::mem::swap(&mut self.coef, &mut rhs.coef);
        }
        *self = rhs.multiply(self);
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
    fn shl(self, rhs: usize) -> Self::Output {
        (&self) << rhs
    }
}

impl<M: Modulo> Shl<u32> for Polynomial<M> {
    type Output = Self;
    fn shl(self, rhs: u32) -> Self::Output {
        self << (rhs as usize)
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
    fn shr(self, rhs: usize) -> Self::Output {
        (&self) >> rhs
    }
}

impl<M: Modulo> Shr<u32> for Polynomial<M> {
    type Output = Self;
    fn shr(self, rhs: u32) -> Self::Output {
        self >> (rhs as usize)
    }
}

impl<M: Modulo> From<Vec<u32>> for Polynomial<M> {
    fn from(mut v: Vec<u32>) -> Self {
        let l = v.len() >> 3 << 3;
        v[..l].chunks_exact_mut(8).for_each(|v| {
            let w =
                unsafe { Modintx8::<M>::load(v.as_ptr() as _) * Modintx8::from_rawval(M::R2X8) };
            unsafe { w.store(v.as_mut_ptr() as _) }
        });
        v[l..]
            .iter_mut()
            .for_each(|v| *v = Modint::<M>::new(*v).val);
        Self { coef: unsafe { std::mem::transmute(v) } }
    }
}

impl<M: Modulo> From<Vec<Modint<M>>> for Polynomial<M> {
    fn from(v: Vec<Modint<M>>) -> Self {
        Self { coef: v }
    }
}

impl<M: Modulo> From<&[Modint<M>]> for Polynomial<M> {
    fn from(value: &[Modint<M>]) -> Self {
        Self { coef: value.to_vec() }
    }
}

impl<M: Modulo> From<Polynomial<M>> for Vec<u32> {
    fn from(mut value: Polynomial<M>) -> Self {
        let l = value.deg() >> 3 << 3;
        value.coef[..l].chunks_exact_mut(8).for_each(|v| {
            let w = unsafe { Modintx8::load(v.as_ptr()) };
            unsafe { Modintx8::from_rawval(w.val()).store(v.as_mut_ptr()) }
        });
        value.coef[l..]
            .iter_mut()
            .for_each(|v| *v = Modint::from_rawval(v.val()));
        unsafe { std::mem::transmute(value.coef) }
    }
}

impl<M: Modulo> From<Polynomial<M>> for Vec<Modint<M>> {
    fn from(value: Polynomial<M>) -> Self {
        value.coef
    }
}

impl<M: Modulo> Zero for Polynomial<M> {
    fn zero() -> Self {
        Self::empty()
    }
}

impl<M: Modulo> One for Polynomial<M> {
    fn one() -> Self {
        Self::from(vec![Modint::one()])
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

        let add = (poly + poly2)
            .coef
            .into_iter()
            .map(|v| v.val())
            .collect::<Vec<_>>();
        assert_eq!(add, vec![6, 6, 7, 10, 17]);
    }

    #[test]
    fn polynomial_sub_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![5, 4, 3, 2, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![1, 2, 4, 8, 16]);

        let sub = (poly - poly2)
            .coef
            .into_iter()
            .map(|v| v.val())
            .collect::<Vec<_>>();
        assert_eq!(sub, vec![4, 2, 998244352, 998244347, 998244338]);

        let poly = Polynomial::<Mod998244353>::from(vec![5, 4, 3, 2, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![1, 2, 4, 8, 16, 5, 8]);

        let sub = (poly - poly2)
            .coef
            .into_iter()
            .map(|v| v.val())
            .collect::<Vec<_>>();
        assert_eq!(
            sub,
            vec![4, 2, 998244352, 998244347, 998244338, 998244348, 998244345]
        );
    }

    #[test]
    fn polynomial_mul_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![5, 4, 3, 2, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![1, 2, 4, 8, 16]);

        let mul = (poly * poly2)
            .coef
            .into_iter()
            .map(|v| v.val())
            .collect::<Vec<_>>();
        assert_eq!(mul, vec![5, 14, 31, 64, 129, 98, 68, 40, 16]);
    }

    #[test]
    fn polynomial_div_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![0, 0, 0, 0, 0, 0, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![998244352, 998244352, 1]);

        let div = (poly / poly2)
            .coef
            .into_iter()
            .map(|v| v.val())
            .collect::<Vec<_>>();
        assert_eq!(div, vec![5, 3, 2, 1, 1]);
    }

    #[test]
    fn polynomial_rem_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![0, 0, 0, 0, 0, 0, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![998244352, 998244352, 1]);

        let rem = (poly % poly2)
            .coef
            .into_iter()
            .map(|v| v.val())
            .collect::<Vec<_>>();
        assert_eq!(rem, vec![5, 8]);
    }

    #[test]
    fn polynomial_inverse_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![
            907649121, 290651129, 813718295, 770591820, 913049957, 587190944, 411145555, 899491439,
            722412549, 182227749,
        ]);
        let inv = poly
            .inv(poly.deg())
            .coef
            .into_iter()
            .map(|v| v.val())
            .collect::<Vec<_>>();

        assert_eq!(
            inv,
            vec![
                827228041, 288540417, 325694325, 929405258, 743378152, 901428113, 379325593,
                870509167, 978731889, 911693879
            ]
        );
    }

    #[test]
    fn polynomial_sqrt_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![0, 0, 9, 12]);
        let inv = poly.sqrt(poly.deg());

        assert!(inv.is_some());
        let inv: Vec<u32> = inv.unwrap().into();
        assert_eq!(inv, vec![0, 3, 2, 332748117]);
    }

    #[test]
    fn polynomial_exp_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![0, 1, 2, 3, 4]);
        let exp = poly.exp(poly.deg());

        assert!(exp.is_some());
        let exp: Vec<u32> = exp.unwrap().into();
        assert_eq!(exp, vec![1, 1, 499122179, 166374064, 291154613]);
    }

    #[test]
    fn polynomial_integral_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4, 5, 6, 7, 8]);
        let inv: Vec<u32> = poly.integral().into();

        assert_eq!(inv, vec![0, 1, 1, 1, 1, 1, 1, 1, 1]);
    }

    #[test]
    fn multipoint_evaluation_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4]);
        let xs = vec![5.into(), 6.into(), 7.into(), 8.into(), 9.into()];
        let ys = poly.multipoint_evaluation(xs);

        assert_eq!(
            ys,
            vec![
                586.into(),
                985.into(),
                1534.into(),
                2257.into(),
                3178.into()
            ]
        );
    }

    #[test]
    fn lagrange_interpolation_test() {
        let xs = vec![5.into(), 6.into(), 7.into(), 8.into(), 9.into()];
        let fs = vec![
            586.into(),
            985.into(),
            1534.into(),
            2257.into(),
            3178.into(),
        ];

        let res = Polynomial::<Mod998244353>::interpolation(xs, fs);
        assert_eq!(
            res.coef,
            vec![1.into(), 2.into(), 3.into(), 4.into(), 0.into()]
        );
    }
}
