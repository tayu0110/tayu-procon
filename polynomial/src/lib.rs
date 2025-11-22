mod impl_ops;
mod ntt_friendly;

use std::mem::transmute;
use std::ops::{Add, Mul};

use convolution::{convolution_mod, hadamard};
use montgomery_modint::{Modulo, MontgomeryModint, MontgomeryModintx8};
use number_theoretic_transform::{minttou32, u32tomint};
use zero_one::{One, Zero};

use crate::ntt_friendly::is_ntt_friendly_mod;

type Modint<M> = MontgomeryModint<M>;
type Modintx8<M> = MontgomeryModintx8<M>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Polynomial<M: Modulo> {
    coef: Vec<Modint<M>>,
}

impl<M: Modulo> Polynomial<M> {
    /// Return an empty Polynomial. This method is as same as `<Self as Zero>::zero()`.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::Mod998244353;
    /// use zero_one::Zero;
    ///
    /// assert_eq!(Polynomial::<Mod998244353>::empty(), Polynomial::<Mod998244353>::zero());
    /// ```
    #[inline]
    pub fn empty() -> Self {
        Self { coef: vec![] }
    }

    pub fn zero() -> Self {
        Self::empty()
    }

    pub fn one() -> Self {
        Self { coef: vec![Modint::one()] }
    }

    /// Returns the number of terms in the polynomial.  
    /// Therefore, the highest degree of `self` is `self.deg() - 1`.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::Mod998244353;
    ///
    /// let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4]);
    /// assert_eq!(poly.deg(), 4);
    /// ```
    #[inline]
    pub fn deg(&self) -> usize {
        self.coef.len()
    }

    /// Multiply all terms in `self` by `s`.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::{Mod998244353, MontgomeryModint};
    ///
    /// let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4]);
    /// assert_eq!(poly.scale(5.into()), Polynomial::from(vec![5, 10, 15, 20]));
    /// ```
    #[inline]
    pub fn scale(mut self, s: Modint<M>) -> Self {
        let sv = Modintx8::splat(s);
        let mut it = self.coef.chunks_exact_mut(8);
        for v in it.by_ref() {
            unsafe { (Modintx8::load(v.as_ptr()) * sv).store(v.as_mut_ptr()) }
        }
        it.into_remainder().iter_mut().for_each(|v| *v *= s);
        self
    }

    /// Evaluate the value of `x` assigned to `self`.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::Mod998244353;
    ///
    /// // 1 + 2x + 3x^2 + 4x^3
    /// let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4]);
    /// assert_eq!(poly.evaluate(0.into()), 1.into());
    /// assert_eq!(poly.evaluate(3.into()), 142.into());
    /// ```
    pub fn evaluate(&self, x: Modint<M>) -> Modint<M> {
        let mut co = Modint::one();
        let mut res = Modint::zero();
        for &c in &self.coef {
            res += co * c;
            co *= x;
        }
        res
    }

    /// Return the lower `new_deg` term of self.  
    /// If `new_deg` is greater than `self.deg()`, adjust and return the `new_deg` term with a zero fill.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::Mod998244353;
    ///
    /// let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4, 5, 6]);
    /// assert_eq!(poly.prefix(3), Polynomial::from(vec![1, 2, 3]));
    /// assert_eq!(poly.prefix(6), poly);
    /// assert_eq!(poly.prefix(10), Polynomial::from(vec![1, 2, 3, 4, 5, 6, 0, 0, 0, 0]));
    /// ```
    #[inline]
    pub fn prefix(&self, new_deg: usize) -> Self {
        let mut res = self.coef.iter().copied().take(new_deg).collect::<Self>();
        res.resize(new_deg);
        res
    }

    /// Returns the first derivative of `self`.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::Mod998244353;
    ///
    /// let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4, 5]);
    /// assert_eq!(poly.derivative(), Polynomial::from(vec![2, 6, 12, 20]));
    /// ```
    #[inline]
    pub fn derivative(&self) -> Self {
        self.coef
            .iter()
            .copied()
            .enumerate()
            .skip(1)
            .map(|(i, p)| p * Modint::new(i as u32))
            .collect::<Self>()
    }

    /// Calculate the indefinite integral.  
    /// The constant term is filled with 0.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::Mod998244353;
    ///
    /// let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4]);
    /// assert_eq!(poly.integral(), Polynomial::from(vec![0, 1, 1, 1, 1]));
    /// ```
    pub fn integral(&self) -> Self {
        self._integral(unsafe { Self::gen_inverse_table(self.deg()) })
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
            let len = coef.len() - 1;
            hadamard(&mut coef[1..], &self.coef[..len]);
            Self { coef }
        }
    }

    // https://37zigen.com/linear-sieve/#i-4
    #[target_feature(enable = "avx", enable = "avx2")]
    unsafe fn gen_inverse_table(deg: usize) -> Vec<Modint<M>> {
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

    #[inline]
    fn multiply(mut self, rhs: &Self) -> Self {
        if self.deg() == 0 || rhs.deg() == 0 {
            return Self::empty();
        }
        self.coef = convolution_mod(self.coef, rhs.coef.clone());
        self
    }

    fn doubling_step_for_inv(&self, g: Self) -> Self {
        debug_assert_eq!(1 << g.deg().trailing_zeros(), g.deg());
        // `g` must be the inverse of `poly` on mod `g.deg()`
        debug_assert_eq!(
            {
                let mut g = self.clone().multiply(&g).prefix(g.deg());
                g.shrink();
                g.coef
            },
            Polynomial::one().coef
        );
        if is_ntt_friendly_mod::<M>(g.deg().next_power_of_two() << 1) {
            return unsafe { ntt_friendly::doubling_step_for_inv(self, g) };
        }

        let size = g.deg();
        ((Self::from(vec![Modint::new(2)]) - self.prefix(size << 1).multiply(&g)).prefix(size << 1)
            * g)
            .prefix(size << 1)
    }

    // reference: https://web.archive.org/web/20220903140644/https://opt-cp.com/fps-fast-algorithms/#toc4
    // reference: https://nyaannyaan.github.io/library/fps/formal-power-series.hpp
    // reference: https://judge.yosupo.jp/submission/68532
    /// Return the inverse of `self` mod x<sup>deg</sup>.
    ///
    /// Since `Self::div()` returns the quotient of a polynomial, it may not match the result of FPS division.  
    /// When performing FPS division, it is necessary to perform multiplication with the result of `self.inv(deg)`, which specifies the required precision in `deg`.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::{Mod998244353, Mod1000000007};
    /// use zero_one::One;
    ///
    /// let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4, 5]);
    /// let mut res = (poly.clone() * poly.inv(5)).prefix(5);
    /// res.shrink();
    /// assert_eq!(res, Polynomial::one());
    ///
    /// let mut res = (poly.clone() * poly.inv(30)).prefix(30);
    /// res.shrink();
    /// assert_eq!(res, Polynomial::one());
    ///
    /// let poly = Polynomial::<Mod1000000007>::from(vec![1, 2, 3, 4, 5]);
    /// let mut res = (poly.clone() * poly.inv(30)).prefix(30);
    /// res.shrink();
    /// assert_eq!(res, Polynomial::one());
    /// ```
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

    /// Remove Leading Zeros.  
    /// Do not perform capacity adjustments such as `Vec::shrink_to_fit`.
    #[inline]
    pub fn shrink(&mut self) {
        let garbage_cnt = self
            .coef
            .iter()
            .rev()
            .take_while(|&&v| v == Modint::zero())
            .count();
        self.resize(self.deg() - garbage_cnt);
    }

    /// Return a pair of `(self / rhs, self % rhs)`.  
    /// For returned values, `Quotient * Divisor + Remainder == self` and `Divisor.deg() > Remainder.deg()` is always satisfied.
    ///
    /// If you need both a quotient and a remainder,  
    /// it may be more efficient to use `self.div_rem(rhs)` than to use `self.div(rhs)` and `self.rem(rhs)` separately.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::Mod998244353;
    ///
    /// let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4, 5, 6, 7, 8]);
    /// let divisor = Polynomial::from(vec![5, 4, 3, 2, 1]);
    /// let (quotient, remainder) = poly.clone().div_rem(divisor.clone());
    /// assert!(divisor.deg() > remainder.deg());
    /// assert_eq!(divisor * quotient + remainder, poly);
    /// ```
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
        if is_ntt_friendly_mod::<M>(m) {
            return unsafe { ntt_friendly::gen_subproduct_tree(xs) };
        }

        let mut sptree = vec![Polynomial::empty(); m * 2];
        for i in 0..m {
            sptree[m + i] = vec![Modint::one(), -*xs.get(i).unwrap_or(&Modint::zero())].into();
        }

        for i in (1..m).rev() {
            let d = (sptree[i << 1].deg() - 1) << 1;
            sptree[i] = sptree[i << 1].clone().multiply(&sptree[(i << 1) | 1]);
            debug_assert_eq!(sptree[i].deg(), ((sptree[i << 1].deg() - 1) << 1) + 1);
            sptree[i << 1].resize(d);
            sptree[(i << 1) | 1].resize(d);
        }
        sptree
    }

    fn transposed_uptree(m: usize, mut subproduct_tree: Vec<Polynomial<M>>) -> Vec<Polynomial<M>> {
        if is_ntt_friendly_mod::<M>(m) {
            return unsafe { ntt_friendly::transposed_uptree(m, subproduct_tree) };
        }
        for i in 1..m {
            let (a, b) = subproduct_tree.split_at_mut(i << 1);
            let n = a[i].deg() >> 1;
            for b in b.iter_mut().take(2) {
                debug_assert_eq!(a[i].deg(), b.deg());
                *b *= a[i].clone();
                b.resize(a[i].deg());
                *b >>= n;
            }
            b.swap(0, 1);
        }
        subproduct_tree
    }

    /// Returns all the results of evaluating self with the elements of `xs`.  
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::{Mod998244353, Mod1000000007};
    ///
    /// let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4]);
    /// let res = poly.multipoint_evaluation(vec![5.into(), 6.into(), 7.into(), 8.into(), 9.into()]);
    /// assert_eq!(res, vec![586.into(), 985.into(), 1534.into(), 2257.into(), 3178.into()]);
    ///
    /// let poly = Polynomial::<Mod1000000007>::from(vec![1, 2, 3, 4]);
    /// let res = poly.multipoint_evaluation(vec![5.into(), 6.into(), 7.into(), 8.into(), 9.into()]);
    /// assert_eq!(res, vec![586.into(), 985.into(), 1534.into(), 2257.into(), 3178.into()]);
    /// ```
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

    /// Derive a polynomial such that substituting `xs[i]` for f(x) for any `i` evaluates to `fs[i]` using Lagrange interpolation.  
    /// It may work with duplicate elements, but it is not recommended because it is not expected.
    ///
    /// Since this method uses NTT multiplication internally, there is no guarantee that it works with anything except for NTT Friendly mods at this time.  
    /// If it is not necessary to restore the coefficients explicitly, you can use `polynomial::interpolation_with_eval` except for the NTT Friendly mod also.
    ///
    /// # Panics
    /// `xs.len()` must be equal to `fs.len()`.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::{Mod998244353, Mod1000000007};
    ///
    /// let coef: Vec<u32> = Polynomial::<Mod998244353>::interpolation(
    ///     vec![5.into(), 6.into(), 7.into(), 8.into(), 9.into()],
    ///     vec![586.into(), 985.into(), 1534.into(), 2257.into(), 3178.into()],
    /// ).into();
    /// assert_eq!(coef, vec![1, 2, 3, 4, 0]);
    ///
    /// let coef: Vec<u32> = Polynomial::<Mod1000000007>::interpolation(
    ///     vec![5.into(), 6.into(), 7.into(), 8.into(), 9.into()],
    ///     vec![586.into(), 985.into(), 1534.into(), 2257.into(), 3178.into()],
    /// ).into();
    /// assert_eq!(coef, vec![1, 2, 3, 4, 0]);
    /// ```
    pub fn interpolation(xs: Vec<Modint<M>>, fs: Vec<Modint<M>>) -> Self {
        let len = xs.len();
        let m = len.next_power_of_two();
        assert_eq!(len, fs.len());
        if len == 0 {
            return Polynomial::empty();
        }

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

        subproduct_tree[m..m + len]
            .iter_mut()
            .zip(fs)
            .for_each(|(v, f)| *v = vec![f / *v.coef.first().unwrap_or(&Modint::zero())].into());
        subproduct_tree[m + len..].fill(Polynomial::empty());

        if is_ntt_friendly_mod::<M>(m) {
            return unsafe { ntt_friendly::interpolation(m, keep, subproduct_tree) };
        }

        for i in 1..m {
            let n = keep[i << 1].deg() >> 1;
            for j in 0..2 {
                keep[(i << 1) | j].resize(n + 1);
                keep[(i << 1) | j].reverse();
            }
        }
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
                let new = kl.deg() + kr.deg() - 1;
                let sh = keep[i].deg() - new;
                keep[i] >>= sh;
            }
            subproduct_tree[i] = l * kr + r * kl;
        }
        subproduct_tree.pop().unwrap()
    }

    /// Calculate a square root of `self` mod x<sup>`deg`</sup>.  
    /// If any result are not found, return `None`.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::Mod998244353;
    ///
    /// let poly = Polynomial::<Mod998244353>::from(vec![0, 0, 9, 12]);
    /// let sqrt = poly.sqrt(4);
    /// assert!(sqrt.is_some());
    /// let sqrt = sqrt.unwrap();
    /// assert_eq!((sqrt.clone() * sqrt).prefix(4), poly);
    /// ```
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

    /// Calculate log f(x) when f(x) is `self`.  
    /// If `self[0]` is not equal to `1`, return `None`.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::Mod998244353;
    ///
    /// let poly = Polynomial::<Mod998244353>::from(vec![1, 2, 3, 4, 5]);
    /// let log = poly.log(poly.deg()).unwrap();
    /// assert_eq!(log.exp(poly.deg()).unwrap(), poly);
    /// ```
    pub fn log(&self, deg: usize) -> Option<Self> {
        (self.deg() >= 1 && self[0] == Modint::one()).then_some(
            (self.derivative() * self.inv(deg))
                ._integral(unsafe { Self::gen_inverse_table(deg) })
                .prefix(deg),
        )
    }

    /// Calculate e<sup>`self`</sup> mod x<sup>`deg`</sup>.  
    /// If `self[0]` is not equal to `0`, this method returns `None`.
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::{Mod998244353, Mod1000000007};
    ///
    /// let poly = Polynomial::<Mod998244353>::from(vec![0, 1, 2, 3, 4]);
    /// let exp = poly.exp(5).unwrap();
    /// assert_eq!(exp.log(5).unwrap(), poly);
    ///
    /// let poly = Polynomial::<Mod1000000007>::from(vec![0, 1, 2, 3, 4]);
    /// let exp = poly.exp(5).unwrap();
    /// assert_eq!(exp.log(5).unwrap(), poly);
    /// ```
    // reference: https://judge.yosupo.jp/submission/70211
    pub fn exp(&self, deg: usize) -> Option<Self> {
        if self.deg() >= 1 && self[0] != Modint::zero() {
            return None;
        }
        if self.deg() == 0 {
            return Some(Polynomial::one());
        }

        if is_ntt_friendly_mod::<M>(self.deg()) {
            return unsafe { ntt_friendly::exp(self, deg) };
        }

        let mut res = Self::one();
        let mut now = 1;
        while now < deg {
            now <<= 1;
            res *= Self::one() - res.log(now).unwrap() + self.prefix(now);
        }
        Some(res.prefix(deg))
    }

    /// Calculate f(x)<sup>n</sup> mod x<sup>deg</sup>.
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

            if deg <= pos.saturating_mul(n as usize) {
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

    // reference: https://twitter.com/risujiroh/status/1215710785000751104?s=20
    // reference: https://nyaannyaan.github.io/library/fps/taylor-shift.hpp.html
    pub fn taylor_shift(mut self, shift: Modint<M>) -> Self {
        let n = self.deg();
        let mut frac = vec![Modint::zero(); n];
        frac[0] = Modint::one();
        for i in 1..n {
            frac[i] = frac[i - 1] * Modint::new(i as u32);
        }
        hadamard(&mut self.coef, &frac);
        self.reverse();
        frac[n - 1] = frac[n - 1].inv();
        for i in (1..n).rev() {
            frac[i - 1] = frac[i] * Modint::new(i as u32);
        }
        let mut exp = self.clone();
        exp[0] = Modint::one();
        let mut f = Modint::one();
        for i in 1..n {
            exp[i] = exp[i - 1] * shift * frac[i] * f;
            f *= Modint::new(i as u32);
        }
        self = (self * exp).prefix(n);
        self.reverse();
        hadamard(&mut self.coef, &frac);
        self
    }

    /// Calculate \[x<sup>n</sup>\](`self`/`other`).  
    /// reference: https://qiita.com/ryuhe1/items/da5acbcce4ac1911f47a
    ///
    /// # Examples
    /// ```rust
    /// use polynomial::Polynomial;
    /// use montgomery_modint::{Mod998244353, MontgomeryModint};
    ///
    /// type Modint = MontgomeryModint<Mod998244353>;
    ///
    /// // Fibonacci Sequence
    /// let p = Polynomial::from(vec![Modint::zero(), Modint::one()]);
    /// let q = Polynomial::from(vec![Modint::one(), -Modint::one(), -Modint::one()]);
    ///
    /// // 0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89, 144, 233, 377, 610, 987
    /// assert_eq!(p.bostan_mori(&q, 0), 0.into());
    /// assert_eq!(p.bostan_mori(&q, 10), 55.into());
    /// assert_eq!(p.bostan_mori(&q, 16), 987.into())
    /// ```
    pub fn bostan_mori(&self, other: &Self, mut n: u64) -> Modint<M> {
        let (mut p, mut q) = (self.clone(), other.clone());
        while n > 0 {
            let mut nq = q.clone();
            nq.coef.iter_mut().skip(1).step_by(2).for_each(|q| *q = -*q);
            let u = p.multiply(&nq);
            let lsb = (n & 1) as usize;
            p = u
                .coef
                .into_iter()
                .enumerate()
                .filter_map(|u| ((u.0 & 1) == lsb).then_some(u.1))
                .collect::<Self>();
            q = (q * nq).coef.into_iter().step_by(2).collect::<Self>();
            n >>= 1;
        }
        p[0] / q[0]
    }
}

impl<M: Modulo> From<Vec<u32>> for Polynomial<M> {
    fn from(mut v: Vec<u32>) -> Self {
        unsafe {
            u32tomint::<M>(&mut v[..]);
            Self { coef: transmute::<Vec<u32>, Vec<MontgomeryModint<M>>>(v) }
        }
    }
}

impl<M: Modulo> From<Vec<Modint<M>>> for Polynomial<M> {
    fn from(v: Vec<Modint<M>>) -> Self {
        Self { coef: v }
    }
}

macro_rules! impl_from {
    ( $( $t:ty ),+ ) => {
        $(
            impl<M: Modulo> From<Vec<$t>> for Polynomial<M> {
                fn from(value: Vec<$t>) -> Self {
                    value.into_iter().collect::<Polynomial<M>>()
                }
            }
        )+
    };
}
impl_from!(i32, i64, u64);

impl<M: Modulo> From<&[Modint<M>]> for Polynomial<M> {
    fn from(value: &[Modint<M>]) -> Self {
        Self { coef: value.to_vec() }
    }
}

impl<M: Modulo> From<Polynomial<M>> for Vec<u32> {
    fn from(mut value: Polynomial<M>) -> Self {
        unsafe {
            minttou32(&mut value.coef[..]);
            transmute(value.coef)
        }
    }
}

impl<M: Modulo> From<Polynomial<M>> for Vec<Modint<M>> {
    fn from(value: Polynomial<M>) -> Self {
        value.coef
    }
}

impl<M: Modulo> FromIterator<u32> for Polynomial<M> {
    fn from_iter<T: IntoIterator<Item = u32>>(iter: T) -> Self {
        let coef = iter.into_iter().collect::<Vec<_>>();
        coef.into()
    }
}

macro_rules! impl_from_iter {
    ( $( $t:ty ),+ ) => {
        $(
            impl<M: Modulo> FromIterator<$t> for Polynomial<M> {
                fn from_iter<T: IntoIterator<Item = $t>>(iter: T) -> Self {
                    Self { coef: iter.into_iter().map(Modint::from).collect() }
                }
            }
        )+
    };
}

impl_from_iter!(Modint<M>, u64, i32, i64);

impl<M: Modulo> IntoIterator for Polynomial<M> {
    type Item = Modint<M>;
    type IntoIter = std::vec::IntoIter<Self::Item>;
    fn into_iter(self) -> Self::IntoIter {
        self.coef.into_iter()
    }
}

impl<M: Modulo> Zero for Polynomial<M> {
    fn zero() -> Self {
        Self::empty()
    }
}

impl<M: Modulo> One for Polynomial<M> {
    fn one() -> Self {
        Self::one()
    }
}

/// Calculate the value of `f(target)` if the value of `f(x)` is known for `x=0..N`.  
/// `fs[i]` denotes the value of `f(x)` for `x`=`i`.
///
/// Since the coefficients are not explicitly restored,  
/// this method does NOT requires NTT multiplication, and <strong>works well even without NTT Friendly mod</strong>.
///
/// reference: https://atcoder.jp/contests/abc208/editorial/2195
///
/// # Examples
/// ```rust
/// use polynomial::interpolation_with_eval;
/// use montgomery_modint::{Mod1000000007, MontgomeryModint};
///
/// type Modint = MontgomeryModint<Mod1000000007>;
///
/// let poly = vec![1.into(), 3.into(), 7.into()];
/// // x^2 + x + 1 = 3*3 + 3 + 1 = 13
/// assert_eq!(interpolation_with_eval(poly, 3.into()), Modint::new(13));
///
/// let poly = vec![4.into(), 16.into(), 106.into(), 484.into(), 1624.into(), 4384.into()];
/// assert_eq!(interpolation_with_eval(poly, 1000000000.into()), Modint::new(999984471));
/// ```
pub fn interpolation_with_eval<M: Modulo>(fs: Vec<Modint<M>>, target: Modint<M>) -> Modint<M> {
    if fs.is_empty() {
        return Modint::zero();
    }

    let n = fs.len() - 1;
    let mut inv = vec![Modint::one(); n + 1];
    inv[n] = (2..n as u32 + 1)
        .map(Modint::new)
        .reduce(Modint::mul)
        .unwrap_or(Modint::one());
    inv[n] = inv[n].inv();
    for i in (1..n).rev() {
        inv[i] = inv[i + 1] * Modint::new(i as u32 + 1);
    }

    let mut lmul = vec![Modint::one(); n + 1];
    for i in 0..n {
        lmul[i + 1] = lmul[i] * (target - Modint::new(i as u32));
    }
    let mut rmul = vec![Modint::one(); n + 1];
    for i in (1..n + 1).rev() {
        rmul[i - 1] = rmul[i] * (target - Modint::new(i as u32));
    }

    let mut res = Modint::zero();
    for i in 0..n + 1 {
        let l = inv[i] * inv[n - i] * lmul[i] * rmul[i] * fs[i];
        if (n - i) & 1 != 0 {
            res -= l;
        } else {
            res += l;
        }
    }
    res
}

/// When given the first d terms of the linear recurrence sequence, find the `k`-th term.
///
/// `c` represents the coefficients for the linear recurrence relation `c[0]a[n-1]+c[1]a[n-2]+...+c[d-1]a[n-k]`.  
/// `a` reprecents the first d terms of the sequence.  
/// `k` is 0-index.
///
/// # Examples
/// ```rust
/// use polynomial::kth_term_of_linearly_recurrent_sequence;
/// use montgomery_modint::Mod998244353;
///
/// // These reprecents the Fibonacci sequence
/// // Fn = Fn-1 + Fn-2
/// let c = vec![1, 1];
/// // 1, 1, 2, 3, 5, 8, 13, 21, 34, ...
/// let a = vec![1, 1];
/// assert_eq!(kth_term_of_linearly_recurrent_sequence::<Mod998244353>(c, a, 8), 34.into());
///
/// // What is this ?
/// // Fn = Fn-1 + 2Fn-2
/// let c = vec![1, 2];
/// // it seems the power of 2...
/// // 1, 2, 4, 8, 16, 32, ...
/// let a = vec![1, 2];
/// assert_eq!(kth_term_of_linearly_recurrent_sequence::<Mod998244353>(c, a, 10), 1024.into());
/// ```
pub fn kth_term_of_linearly_recurrent_sequence<M: Modulo>(
    c: impl Into<Polynomial<M>>,
    a: impl Into<Polynomial<M>>,
    k: u64,
) -> Modint<M> {
    let (mut q, a): (Polynomial<M>, Polynomial<M>) = (c.into(), a.into());
    q.coef.iter_mut().for_each(|c| *c = -*c);
    q.coef.insert(0, Modint::one());
    let p = a.multiply(&q).prefix(q.deg() - 1);
    p.bostan_mori(&q, k)
}

pub fn berlekamp_massey<M: Modulo>(a: impl Into<Polynomial<M>>) -> Polynomial<M> {
    let a: Polynomial<M> = a.into();
    let n = a.deg();
    let (mut b, mut c) = (vec![Modint::one()], vec![Modint::one()]);
    b.reserve(n);
    c.reserve(n);
    let mut y = Modint::one();
    for i in 1..=n {
        let x = c
            .iter()
            .zip(&a.coef[i - c.len()..])
            .map(|(c, a)| *c * *a)
            .reduce(Modint::add)
            .unwrap();
        b.push(Modint::zero());
        if x == Modint::zero() {
            continue;
        }
        let freq = x / y;
        if c.len() < b.len() {
            let t = c.clone();
            c.reverse();
            c.resize(b.len(), Modint::zero());
            c.reverse();
            c.iter_mut().zip(b).for_each(|(c, b)| *c -= freq * b);
            b = t;
            y = x;
        } else {
            c.iter_mut()
                .rev()
                .zip(b.iter().rev())
                .for_each(|(c, b)| *c -= freq * *b);
        }
    }
    c.reverse();
    c.into()
}

#[cfg(test)]
mod tests {
    use super::Polynomial;
    use montgomery_modint::{Mod1000000007, Mod998244353, MontgomeryModint};
    use rand::{thread_rng, Rng};

    #[test]
    fn polynomial_add_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![5, 4, 3, 2, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![1, 2, 4, 8, 16]);

        let add: Vec<u32> = (poly + poly2).into();
        assert_eq!(add, vec![6, 6, 7, 10, 17]);
    }

    #[test]
    fn polynomial_sub_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![5, 4, 3, 2, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![1, 2, 4, 8, 16]);

        let sub: Vec<u32> = (poly - poly2).into();
        assert_eq!(sub, vec![4, 2, 998244352, 998244347, 998244338]);

        let poly = Polynomial::<Mod998244353>::from(vec![5, 4, 3, 2, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![1, 2, 4, 8, 16, 5, 8]);

        let sub: Vec<u32> = (poly - poly2).into();
        assert_eq!(
            sub,
            vec![4, 2, 998244352, 998244347, 998244338, 998244348, 998244345]
        );
    }

    #[test]
    fn polynomial_mul_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![5, 4, 3, 2, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![1, 2, 4, 8, 16]);

        let mul: Vec<u32> = (poly * poly2).into();
        assert_eq!(mul, vec![5, 14, 31, 64, 129, 98, 68, 40, 16]);
    }

    #[test]
    fn polynomial_div_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![0, 0, 0, 0, 0, 0, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![998244352, 998244352, 1]);

        let div: Vec<u32> = (poly / poly2).into();
        assert_eq!(div, vec![5, 3, 2, 1, 1]);
    }

    #[test]
    fn polynomial_rem_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![0, 0, 0, 0, 0, 0, 1]);
        let poly2 = Polynomial::<Mod998244353>::from(vec![998244352, 998244352, 1]);

        let rem: Vec<u32> = (poly % poly2).into();
        assert_eq!(rem, vec![5, 8]);
    }

    #[test]
    fn polynomial_inverse_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![
            907649121, 290651129, 813718295, 770591820, 913049957, 587190944, 411145555, 899491439,
            722412549, 182227749,
        ]);
        let inv: Vec<u32> = poly.inv(poly.deg()).into();

        assert_eq!(
            inv,
            vec![
                827228041, 288540417, 325694325, 929405258, 743378152, 901428113, 379325593,
                870509167, 978731889, 911693879
            ]
        );
    }

    #[test]
    fn polynomial_inverse_non_ntt_friendly_test() {
        let mut rng = thread_rng();

        for _ in 0..100 {
            let n = rng.gen_range(1..5usize);
            let poly = Polynomial::<Mod1000000007>::from(
                (0..n)
                    .map(|_| rng.gen_range(1u32..10).into())
                    .collect::<Vec<MontgomeryModint<Mod1000000007>>>(),
            );
            let inv = poly.inv(n);
            assert_eq!((poly * inv).prefix(n), Polynomial::one().prefix(n));
        }
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
    fn polynomial_exp_non_ntt_friendly_test() {
        let mut rng = thread_rng();

        for _ in 0..100 {
            let n = rng.gen_range(1..10);
            let fs = (0..n)
                .map(|i| rng.gen_range(0u32..=i as u32))
                .collect::<Vec<_>>();
            let poly = Polynomial::<Mod1000000007>::from(fs);
            let exp = poly.exp(n).unwrap();
            eprintln!("exp: {exp:?}");
            assert_eq!(exp.log(n), Some(poly));
        }
    }

    #[test]
    fn polynomial_log_test() {
        let poly = Polynomial::<Mod998244353>::from(vec![1, 1, 499122179, 166374064, 291154613]);
        let log = poly.log(poly.deg());

        assert!(log.is_some());
        let log: Vec<u32> = log.unwrap().into();
        assert_eq!(log, vec![0, 1, 2, 3, 4]);
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
    fn polynomial_interpolation_test() {
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

    #[test]
    fn polynomial_interpolation_non_ntt_friendly_test() {
        type Modint = MontgomeryModint<Mod1000000007>;

        let mut rng = thread_rng();

        for _ in 0..100 {
            let n = rng.gen_range(1..10);
            let xs = (0..n).map(Modint::new).collect::<Vec<_>>();
            let fs = (0..n)
                .map(|_| rng.gen_range(0u32..10).into())
                .collect::<Vec<_>>();
            let poly = Polynomial::<Mod1000000007>::interpolation(xs.clone(), fs.clone());
            eprintln!("n: {n}, fs: {fs:?}, poly: {poly:?}");

            for (x, f) in xs.into_iter().zip(fs) {
                assert_eq!(poly.evaluate(x), f);
            }
        }
    }
}
