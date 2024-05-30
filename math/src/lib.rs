#[cfg(feature = "const_methods")]
mod const_methods;
mod montgomery;

use std::{collections::HashMap, iter::once, ops::Index};

#[cfg(feature = "const_methods")]
pub use const_methods::*;
pub use montgomery::Montgomery;
use simple_rand::xor_shift;

pub struct ExtendedGcd<T> {
    pub gcd: T,
    pub coef: [T; 2],
    pub neg: [bool; 2],
}

pub struct Factors<T: MathInt> {
    current: T,
}
macro_rules! impl_factors {
    ( $( $t:ty ),* ) => {
        $(
            impl Iterator for Factors<$t> {
                type Item = ($t, u32);
                fn next(&mut self) -> Option<Self::Item> {
                    (self.current > 0).then(|| {
                        if self.current & 1 == 0 {
                            let tr = self.current.trailing_zeros();
                            self.current >>= tr;
                            return Some((2, tr));
                        }

                        self.current.one_of_the_prime_factors().map(|fac| {
                            let mut cnt = 0;
                            while self.current % fac == 0 {
                                self.current /= fac;
                                cnt += 1;
                            }
                            (fac, cnt)
                        })
                    })?
                }
            }
        )*
    };
}

impl_factors!(u8, u16, u32, u64, usize, i8, i16, i32, i64, isize);

pub trait MathInt: Sized + Copy {
    /// Return the greatest common divisor of `self` and `other`.
    /// `gcd(0, 0)` is assumed to be `0`.
    ///
    /// The return value is always non-negative.
    /// Therefore, this method panics if two signed integer minimums (e.g., `i32::MIN`) are passed as arguments
    /// because it may not return the correct result.
    ///
    /// # Panics
    /// - One of the arguments must always be greater than the minimum value. (for only signed integer)
    fn gcd(self, other: Self) -> Self;
    /// Return the least common multiple of `self` and `other`.  
    /// The return value is always non-negative.
    ///
    /// # Panics
    /// - Because this method can overflow in multiplication, panic may occur (in debug mode)
    fn lcm(self, other: Self) -> Self;
    /// Return `gcd(a, b)`, `a`, `b` satisfying `self * a + other * b = gcd(a, b)`.
    ///
    /// Since the solution can be negative, for unsigned integers,
    /// the solution is expressed as a combination of the absolute value of the solution and the sign.
    ///
    /// For signed integers, the returned sign has no meaning and is always `true`.  
    /// `gcd(a, b)` is always non-negative.
    ///
    /// # Panics
    /// - `gcd(a, b).abs()` must be less than or equal to Self::MAX (for signed integer)
    ///
    /// # Examples
    /// ```rust
    /// use math::{MathInt, ExtendedGcd};
    ///
    /// // Solve the equation 7x + 11y = 1.
    /// let ExtendedGcd { gcd, mut coef, neg } = 7u32.extended_gcd(11);
    /// // gcd(7, 11) == 1
    /// assert_eq!(gcd, 1);
    ///
    /// coef[0] *= 7;
    /// coef[1] *= 11;
    /// // if neg[i] is `true`, coef[i] is negative.
    /// let x = if neg[0] { coef[0].wrapping_neg() } else { coef[0] };
    /// let y = if neg[1] { coef[1].wrapping_neg() } else { coef[1] };
    /// assert_eq!(x.wrapping_add(y), gcd);
    /// ```
    fn extended_gcd(self, other: Self) -> ExtendedGcd<Self>;
    /// Return the multiplicative inverse of `self` with `modulus` as the law.
    /// If such number is not found, return `None`.
    ///
    /// # Panics
    /// - `modulus > 0` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use math::MathInt;
    ///
    /// assert_eq!(3u32.inverse_mod(7), Some(5));
    /// assert_eq!(5u32.inverse_mod(8), Some(5));
    /// assert_eq!(2u32.inverse_mod(8), None);
    /// ```
    fn inverse_mod(self, modulus: Self) -> Option<Self>;
    /// Returns the `exp` power of `self` using `modulus` as the law.
    ///
    /// # Panics
    /// - `modulus > 0` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use math::MathInt;
    ///
    /// assert_eq!(2u32.pow_mod(31, 998244353), (1 << 31) % 998244353);
    /// assert_eq!(3u32.pow_mod(20, 998244353), 3u32.pow(20) % 998244353);
    /// ```
    fn pow_mod(self, exp: u64, modulus: Self) -> Self;
    /// Return `x` satisfying `base.pow_mod(x, modulus) == self % modulus`.
    /// If such `x` is not found, return `None`.
    ///
    /// # Panics
    /// - `modulus > 0` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use math::MathInt;
    ///
    /// assert_eq!(1u32.log_mod(2, 5), Some(0));
    /// assert_eq!(7u32.log_mod(4, 10), None);
    /// assert_eq!(6u32.log_mod(8, 10), Some(4));
    /// assert_eq!(2u32.log_mod(5, 11), None);
    /// assert_eq!(9u32.log_mod(5, 11), Some(4));
    /// assert_eq!(0u32.log_mod(0, 1), Some(0));
    /// assert_eq!(2u32.log_mod(0, 4), None);
    /// assert_eq!(6u32.log_mod(6, 9), Some(1));
    /// ```
    fn log_mod(self, base: Self, modulus: Self) -> Option<Self>;
    /// Return `x` satisfying `x.pow_mod(2, modulus) == self % modulus`.
    /// If not found, return `None`.
    ///
    /// Tonelli-Shanks algorithm requires that the law is prime,
    /// so `modulus` will not accept non-prime numbers.
    ///
    /// # Panics
    /// - `modulus > 0` must be satisfied (for signed integer)
    /// - `modulus.is_prime() == true` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use math::MathInt;
    ///
    /// assert_eq!(0u32.sqrt_mod(5).map(|sq| sq * sq % 5), Some(0));
    /// assert_eq!(1u32.sqrt_mod(5).map(|sq| sq * sq % 5), Some(1));
    /// assert_eq!(2u32.sqrt_mod(5), None);
    /// assert_eq!(3u32.sqrt_mod(5), None);
    /// assert_eq!(4u32.sqrt_mod(5).map(|sq| sq * sq % 5), Some(4));
    /// assert_eq!(119811886u32.sqrt_mod(197136769).map(|sq| sq as u64 * sq as u64 % 197136769), Some(119811886));
    /// ```
    fn sqrt_mod(self, modulus: Self) -> Option<Self>;
    /// If x satisfies x = p (mod m) and x = q (mod n) is found, return Some((x, lcm(m,n))).
    /// Otherwise, return None.
    /// ```ignore
    /// p + ma = x
    /// q + nb = x
    ///     => p + ma = q + nb
    ///     => ma - nb = q - p
    ///     => ma = q - p (mod n)
    /// ```
    /// `self = p, modulus = m, other = q, other_modulus = n`
    ///
    /// # Panics
    /// - Both `p < m` and `q < n` must be satisfied.
    /// - Both `m > 0` and `n > 0` must be satisfied. (for signed integer)
    /// - `lcm(modulus, other_modulus) <= Self::MAX` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use math::MathInt;
    ///
    /// assert_eq!(2u32.crt(3, 3, 5), Some((8, 15)));
    /// assert_eq!(3u32.crt(5, 2, 7), Some((23, 35)));
    /// assert_eq!(2u32.crt(7, 2, 3), Some((2, 21)));
    /// assert_eq!(2u32.crt(3, 23, 35), Some((23, 105)));
    /// ```
    fn crt(self, modulus: Self, other: Self, other_modulus: Self) -> Option<(Self, Self)>;
    /// Reference : https://doc.rust-lang.org/src/core/num/uint_macros.rs.html
    /// This is as same as Rust unstable feature `isqrt`, so define here. When `isqrt` is stabilized, remove this method.
    ///
    /// # Panics
    /// - `self >= 0` must be satisfied. (for signed integer)
    fn sqrti(self) -> Self;
    /// Check if `self` is a prime number.
    ///
    /// If `self` is negative, always return `false`.
    ///
    /// # Examples
    /// ```rust
    /// use math::MathInt;
    ///
    /// assert!(2u32.is_prime());
    /// assert!(5u32.is_prime());
    /// assert!(998244353u32.is_prime());
    /// assert!(!4u32.is_prime());
    /// assert!(!561u32.is_prime());
    /// ```
    fn is_prime(self) -> bool;
    /// Find one of the prime factors of `self`.
    /// If not found, return `None`.
    ///
    /// If `self` is negative, always return `None`.
    ///
    /// This method uses Pollard's Rho algorithm.
    fn one_of_the_prime_factors(self) -> Option<Self>;
    /// Return an iterator that enumerates prime factors and their number.
    ///
    /// The order of prime factors returned by the iterator is *not defined*.
    /// `1` is not listed.
    ///
    /// If `self` is negative, the iterator always returns `None`.
    ///
    /// # Examples
    /// ```rust
    /// use math::MathInt;
    ///
    /// let mut factors = 108108u32.factorize().collect::<Vec<_>>();
    ///
    /// // Sorting is required to enumerate prime factors in ascending order.
    /// factors.sort();
    /// assert_eq!(factors, vec![(2, 2), (3, 3), (7, 1), (11, 1), (13, 1)]);
    ///
    /// assert_eq!(factors.iter().map(|&(f, c)| f.pow(c)).product::<u32>(), 108108);
    /// ```
    fn factorize(self) -> Factors<Self>;
    /// Return the list of the divisors of `self`.
    /// The order of divisors is *not defined*.
    ///
    /// `1` is included in list.
    ///
    /// If `self` is negative, always return an empty `Vec`.
    ///
    /// # Examples
    /// ```rust
    /// use math::MathInt;
    ///
    /// let mut divisors = 108u32.divisors();
    ///
    /// // Sorting is required to enumerate divisors in ascending order.
    /// divisors.sort();
    /// assert_eq!(divisors, vec![1, 2, 3, 4, 6, 9, 12, 18, 27, 36, 54, 108])
    /// ```
    fn divisors(self) -> Vec<Self>;
    /// Find one of the primitive roots of `self`.
    ///
    /// # Panics
    /// - `self.is_prime() == true` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use math::MathInt;
    ///
    /// assert_eq!(2u32.primitive_root(), 1);
    /// assert_eq!(3u32.primitive_root(), 2);
    /// assert_eq!(5u32.primitive_root(), 2);
    /// assert_eq!(7u32.primitive_root(), 3);
    /// assert_eq!(11u32.primitive_root(), 2);
    /// assert_eq!(13u32.primitive_root(), 2);
    /// assert_eq!(17u32.primitive_root(), 3);
    /// assert_eq!(19u32.primitive_root(), 2);
    /// ```
    fn primitive_root(self) -> Self;
    /// Return the number of primes less than or qeual to `self`.
    ///
    /// If `self < 2` is satisfied, always return `0`.
    fn count_primes(self) -> usize;
}

macro_rules! overflow_err {
    ( $method:literal ) => {
        ::std::concat!("Overflow occurs in ", $method, " for signed integer")
    };
}

macro_rules! impl_math_int_unsigned {
    ( $t:ty, $st:ty, $expand:ty, $( $witness:expr ),* ) => {
        impl MathInt for $t {
            fn gcd(mut self, mut other: Self) -> Self {
                while other != 0 {
                    (self, other) = (other, self % other);
                }
                self
            }

            fn lcm(self, other: Self) -> Self {
                if self == 0 || other == 0 {
                    return 0;
                }
                self / self.gcd(other) * other
            }

            fn extended_gcd(self, other: Self) -> ExtendedGcd<Self> {
                let (mut s, mut sx, mut sy) = (self, 1, 0);
                let (mut t, mut tx, mut ty) = (other, 0, 1);
                let mut neg = 0;
                while t != 0 {
                    let d = s / t;
                    let u = s - t * d;
                    let (ux, uy) = (sx + tx * d, sy + ty * d);
                    (s, sx, sy, t, tx, ty, neg) = (t, tx, ty, u, ux, uy, neg + 1);
                }

                ExtendedGcd {
                    gcd: s,
                    coef: [sx, sy],
                    neg: [
                        neg > 2 && neg & 1 == 1 && sx != 0,
                        neg > 1 + (self < other) as i32 && neg & 1 == 0 && sy != 0,
                    ],
                }
            }

            fn inverse_mod(self, modulus: Self) -> Option<Self> {
                assert!(modulus > 0);
                let ExtendedGcd { gcd, coef, neg } = self.extended_gcd(modulus);

                (gcd == 1).then(|| if neg[0] { modulus - coef[0] } else { coef[0] })
            }

            fn pow_mod(self, mut exp: u64, modulus: Self) -> Self {
                assert!(modulus > 0);
                if modulus == 1 {
                    return 0;
                }
                let a = self % modulus;
                if exp == 0 || a == 1 {
                    return 1;
                }
                if exp == 1 {
                    return a;
                }

                if modulus & 1 == 1 {
                    let mont = Montgomery::<Self>::new(modulus);
                    return mont.reduce(mont.pow(mont.convert(a), exp));
                }

                // If modulus is even, Montgomery multiplication cannot be used.
                // In this case, modulus=modulus' * 2^k (modulus' is odd), and the CRT restoration can be done as `pow_mod(a,exp,modulus')` and `pow_mod(a,exp,2^k)`.
                let s = modulus.trailing_zeros();
                let r = a.pow_mod(exp, modulus >> s);
                assert!(r < modulus >> s);
                let (mut res, mut val) = (1 as $t, a);
                while exp > 0 {
                    if exp & 1 != 0 {
                        res = res.wrapping_mul(val);
                    }
                    val = val.wrapping_mul(val);
                    exp >>= 1;
                }
                res &= (1 << s) - 1;

                if modulus == 1 << s {
                    res
                } else {
                    r.crt(modulus >> s, res, 1 << s).map(|r| r.0)
                        .expect("Unexpected panic: `crt` may have bugs")
                }
            }

            fn log_mod(self, base: Self, modulus: Self) -> Option<Self> {
                assert!(modulus > 0);
                let (a, b) = (base % modulus, self % modulus);
                if modulus == 1 || b == 1 {
                    return Some(0);
                }

                let ExtendedGcd { gcd, coef, neg } = a.extended_gcd(modulus);
                if gcd != 1 {
                    return (b % gcd == 0).then(|| {
                        let (na, nb, nm) = (a / gcd, b / gcd, modulus / gcd);
                        let inv_na = na
                            .inverse_mod(nm)
                            .expect("Internal Error: inverse_mod may have bugs");
                        (((nb as $expand * inv_na as $expand) % modulus as $expand) as Self)
                            .log_mod(a, nm)
                            .map(|res| res + 1)
                    })?;
                }

                let n = (modulus as f64).sqrt().ceil() as Self;
                assert!(n.saturating_mul(n) >= modulus);
                let mut map = HashMap::new();
                let mut aq = 1;
                for i in 0..n {
                    map.entry(aq).or_insert(i);
                    aq = ((aq as $expand * a as $expand) % modulus as $expand) as Self;
                }

                let inv_a = (if neg[0] { modulus - coef[0] } else { coef[0] }).pow_mod(n as u64, modulus);
                let mut ap = b;
                for p in 0..=n {
                    if let Some(q) = map.get(&ap) {
                        return Some(p * n + q);
                    }
                    ap = ((ap as $expand * inv_a as $expand) % modulus as $expand) as Self;
                }

                None
            }

            fn sqrt_mod(self, modulus: Self) -> Option<Self> {
                assert!(modulus.is_prime());
                if modulus == 2 {
                    let res = self & 1;
                    return Some(res);
                }
                let mont = Montgomery::<Self>::new(modulus);
                let mn = mont.convert(self);
                if mn == 0 {
                    return Some(0);
                }

                if modulus & 0b11 == 3 {
                    let s = mont.reduce(mont.pow(mn, (modulus as u64 + 1) >> 2));
                    let t = modulus - s;
                    return Some(s.min(t));
                }

                if mont.pow(mn, (modulus as u64 - 1) >> 1) != mont.one() {
                    return None;
                }

                let mut rng =
                    xor_shift(381928476372819).map(|b| mont.convert(b as Self % (modulus - 2) + 2));
                loop {
                    let b = rng.next()?;
                    if mont.pow(b, (modulus as u64 - 1) >> 1) != mont.one() {
                        let q = (modulus - 1).trailing_zeros() as u64;
                        let s = (modulus as u64 - 1) >> q;

                        let mut x = mont.pow(mn, (s + 1) >> 1);
                        let mut x2 = mont.multiply(x, x);
                        let mut b = mont.pow(b, s);
                        // because `modulus` is a prime number,
                        // so pow(val, modulus - 2) is equivalent to inv(val, modulus)
                        let mninv = mont.pow(mn, modulus as u64 - 2);

                        let mut shift = 2;
                        while x2 != mn {
                            let diff = mont.multiply(mninv, x2);
                            if mont.pow(diff, 1 << (q - shift)) != mont.one() {
                                x = mont.multiply(x, b);
                                b = mont.multiply(b, b);
                                x2 = mont.multiply(x2, b);
                            } else {
                                b = mont.multiply(b, b);
                            }
                            shift += 1;
                        }
                        break Some(mont.reduce(x));
                    }
                }
            }

            fn crt(self, modulus: Self, other: Self, other_modulus: Self) -> Option<(Self, Self)> {
                assert!(self < modulus && other < other_modulus);

                if other < self {
                    return other.crt(other_modulus, self, modulus);
                }

                if self == other {
                    return Some((self, modulus.lcm(other_modulus)));
                }

                let w = other - self;
                let ExtendedGcd { gcd, coef, neg } = modulus.extended_gcd(other_modulus);
                (w % gcd == 0).then(|| {
                    let inv = if neg[0] { other_modulus - coef[0] } else { coef[0] };
                    let k: Self = (inv as $expand * (w / gcd) as $expand % (other_modulus / gcd) as $expand)
                        .try_into()
                        .expect("lcm(modulus, other_modulus) is too large.");
                    let res = self + modulus * k;
                    debug_assert_eq!(res % modulus, self);
                    debug_assert_eq!(res % other_modulus, other);
                    (res, modulus / gcd * other_modulus)
                })
            }

            fn sqrti(self) -> Self {
                if self < 2 {
                    return self;
                }

                let mut op = self;
                let mut res = 0;
                let mut one = 1 << (self.ilog2() & !1);

                while one != 0 {
                    if op >= res + one {
                        op -= res + one;
                        res = (res >> 1) + one;
                    } else {
                        res >>= 1;
                    }
                    one >>= 2;
                }

                res
            }

            fn is_prime(self) -> bool {
                if self == 1 || self & 1 == 0 {
                    return self == 2;
                }

                let s = (self - 1).trailing_zeros();
                let t = (self - 1) >> s;
                let mont = Montgomery::<Self>::new(self);

                [$( $witness ),*]
                    .iter()
                    .map(|&a| mont.convert(a))
                    .filter(|&a| a != 0)
                    .all(|a| {
                        let at = mont.pow(a, t as u64);
                        // a^t = 1 (mod p) or a^t = -1 (mod p)
                        if at == mont.one() || at == self - mont.one() {
                            return true;
                        }

                        // found i satisfying a^((2^i)*t) = -1 (mod p)
                        (1..s)
                            .scan(at, |at, _| {
                                *at = mont.multiply(*at, *at);
                                Some(*at)
                            })
                            .any(|at| at == self - mont.one())
                    })
            }

            fn one_of_the_prime_factors(self) -> Option<Self> {
                // 1 is trival prime factor. So return None.
                if self <= 1 {
                    return None;
                }
                if self & 1 == 0 {
                    return Some(2);
                }

                // If self is prime number, self has no divisors of ifself.
                // So return itself.
                if self.is_prime() {
                    return Some(self);
                }

                let m = (self as f64).powf(0.125).round() as Self + 1;
                let mont = Montgomery::<Self>::new(self);
                let mut g = 1;

                for c in (1..self).map(|c| mont.convert(c)) {
                    let mut y = 0;
                    let mut q = mont.one();

                    'base: for r in (0..).map(|i| 1 << i) {
                        let x = y;
                        (r..=(3 * r) >> 2).for_each(|_| y = mont.add(mont.multiply(y, y), c));
                        for k in (((3 * r) >> 2)..r).step_by(m as usize) {
                            let ys = y;
                            (0..m.min(r - k)).for_each(|_| {
                                y = mont.add(mont.multiply(y, y), c);
                                q = mont.multiply(q, mont.sub(x, y));
                            });
                            g = mont.reduce(q).gcd(self);
                            if g != 1 {
                                if g == self {
                                    y = mont.add(mont.multiply(ys, ys), c);
                                    while mont.reduce(mont.sub(x, y)).gcd(self) == 1 {
                                        y = mont.add(mont.multiply(y, y), c);
                                    }
                                    g = mont.reduce(mont.sub(x, y)).gcd(self);
                                }
                                break 'base;
                            }
                        }
                    }

                    if g != self {
                        break;
                    }
                }

                g.one_of_the_prime_factors()
            }

            fn factorize(self) -> Factors<Self> {
                Factors { current: self }
            }

            fn divisors(self) -> Vec<Self> {
                let mut f = self.factorize().collect::<Vec<_>>();
                f.sort();

                let mut res = vec![1];
                for (c, cnt) in f {
                    let mut now = 1;
                    let len = res.len();
                    for _ in 0..cnt {
                        now *= c;
                        for i in 0..len {
                            let new = res[i] * now;
                            res.push(new);
                        }
                    }
                }

                res
            }

            fn primitive_root(self) -> Self {
                if self == 2 {
                    return 1;
                }

                assert!(self.is_prime());

                let factor = (self - 1)
                    .factorize()
                    .map(|v| (self - 1) / v.0)
                    .collect::<Vec<_>>();
                let mont = Montgomery::<Self>::new(self);
                (1..)
                    .map(|g| mont.convert(g))
                    .find_map(|g| {
                        factor
                            .iter()
                            .all(|&f| mont.pow(g, f as u64) != mont.one())
                            .then_some(mont.reduce(g) % self)
                    })
                    .unwrap()
            }

            // reference : https://judge.yosupo.jp/submission/61553
            fn count_primes(self) -> usize {
                if self <= 2 {
                    return (self as usize).saturating_sub(1);
                }
                let v = self.sqrti() as usize;
                let mut s = (v + 1) / 2;
                let mut smalls = (0..s).collect::<Vec<_>>();
                let mut roughs = (0..s).map(|s| 2 * s + 1).collect::<Vec<_>>();
                let mut larges = (0..s).map(|s| (self as usize / (2 * s + 1) - 1) / 2).collect::<Vec<_>>();
                let mut skip = vec![false; v + 1];
                let mut pc = 0;
                for p in (3..=v).step_by(2) {
                    if !skip[p] {
                        let q = p * p;
                        if q * q > self as usize {
                            break;
                        }
                        skip[p] = true;
                        (q..=v).step_by(2 * p).for_each(|i| skip[i] = true);
                        let mut ns = 0;
                        for k in 0..s {
                            let i = roughs[k];
                            if skip[i] {
                                continue;
                            }
                            let d = i * p;
                            larges[ns] = larges[k] + pc - if d <= v { larges[smalls[d >> 1] - pc] } else { smalls[(self as usize / d - 1) >> 1] };
                            roughs[ns] = i;
                            ns += 1;
                        }
                        s = ns;
                        let mut i = (v - 1) >> 1;
                        let mut j = ((v / p) - 1) | 1;
                        while j >= p {
                            let c = smalls[j >> 1] - pc;
                            let e = (j * p) >> 1;
                            while i >= e {
                                smalls[i] -= c;
                                i -= 1;
                            }
                            j -= 2;
                        }
                        pc += 1;
                    }
                }
                larges[0] += pc.wrapping_sub(1).wrapping_mul(2).wrapping_add(s) * (s - 1) / 2;
                (1..s).for_each(|k| larges[0] -= larges[k]);
                for l in 1..s {
                    let q = roughs[l];
                    let m = self as usize / q;
                    let e = smalls[(m / q - 1) >> 1] - pc;
                    if e < l + 1 {
                        break;
                    }
                    let mut t = 0;
                    for k in l + 1..=e {
                        t += smalls[(m / roughs[k] - 1) >> 1];
                    }
                    larges[0] += t - (e - l) * (pc + l - 1);
                }
                larges[0] + 1
            }
        }

        impl MathInt for $st {
            fn gcd(self, other: Self) -> Self {
                self.unsigned_abs()
                    .gcd(other.unsigned_abs())
                    .try_into()
                    .expect(overflow_err!("MathInt::gcd"))
            }

            fn lcm(self, other: Self) -> Self {
                self.unsigned_abs()
                    .lcm(other.unsigned_abs())
                    .try_into()
                    .expect(overflow_err!("MathInt::lcm"))
            }

            fn extended_gcd(self, other: Self) -> ExtendedGcd<Self> {
                let (mut s, mut sx, mut sy) = (self, 1, 0);
                let (mut t, mut tx, mut ty) = (other, 0, 1);
                while t != 0 {
                    let d = s / t;
                    let u = s - t * d;
                    let (ux, uy) = (sx - tx * d, sy - ty * d);
                    (s, sx, sy, t, tx, ty) = (t, tx, ty, u, ux, uy);
                }

                if s < 0 {
                    const ERR: &str = overflow_err!("MathInt::extended_gcd");
                    s = s.checked_neg().expect(ERR);
                    sx = s.checked_neg().expect(ERR);
                    sy = s.checked_neg().expect(ERR);
                }

                ExtendedGcd { gcd: s, coef: [sx, sy], neg: [true; 2] }
            }

            fn inverse_mod(self, modulus: Self) -> Option<Self> {
                assert!(modulus > 0);
                (self.rem_euclid(modulus) as $t)
                    .inverse_mod(modulus as $t)
                    .map(|inv| inv as Self)
            }

            fn pow_mod(self, exp: u64, modulus: Self) -> Self {
                assert!(modulus > 0);
                (self.rem_euclid(modulus) as $t).pow_mod(exp, modulus as $t) as Self
            }

            fn log_mod(self, base: Self, modulus: Self) -> Option<Self> {
                assert!(modulus > 0);
                (self.rem_euclid(modulus) as $t)
                    .log_mod(base.rem_euclid(modulus) as $t, modulus as $t)
                    .map(|log| log as Self)
            }

            fn sqrt_mod(self, modulus: Self) -> Option<Self> {
                assert!(modulus > 0);
                (self.rem_euclid(modulus) as $t)
                    .sqrt_mod(modulus as $t)
                    .map(|sq| sq as Self)
            }

            fn crt(self, modulus: Self, other: Self, other_modulus: Self) -> Option<(Self, Self)> {
                assert!(modulus > 0 && other_modulus > 0);
                (self.rem_euclid(modulus) as $t)
                    .crt(
                        modulus as $t,
                        other.rem_euclid(other_modulus) as $t,
                        other_modulus as $t,
                    )
                    .map(|(x, lcm)| {
                        (
                            x.try_into().expect(overflow_err!("MathInt::crt")),
                            lcm.try_into().expect(overflow_err!("MathInt::crt")),
                        )
                    })
            }

            fn sqrti(self) -> Self {
                assert!(self >= 0);
                (self as $t).sqrti() as Self
            }

            fn is_prime(self) -> bool {
                self > 1 && (self as $t).is_prime()
            }

            fn one_of_the_prime_factors(self) -> Option<Self> {
                self.is_positive()
                    .then(|| (self as $t).one_of_the_prime_factors().map(|f| f as Self))?
            }

            fn factorize(self) -> Factors<Self> {
                Factors { current: self }
            }

            fn divisors(self) -> Vec<Self> {
                if self <= 0 {
                    return vec![];
                }

                (self as $t)
                    .divisors()
                    .into_iter()
                    .map(|d| d as Self)
                    .collect()
            }

            fn primitive_root(self) -> Self {
                assert!(self >= 0);
                (self as $t).primitive_root() as Self
            }

            fn count_primes(self) -> usize {
                if self < 2 {
                    return 0;
                }
                (self as $t).count_primes()
            }
        }
    };
}

impl_math_int_unsigned!(u8, i8, u16, 2, 7, 61);
impl_math_int_unsigned!(u16, i16, u32, 2, 7, 61);
impl_math_int_unsigned!(u32, i32, u64, 2, 7, 61);
impl_math_int_unsigned!(u64, i64, u128, 2, 325, 9375, 28178, 450775, 9780504, 1795265022);
impl_math_int_unsigned!(usize, isize, u128, 2, 325, 9375, 28178, 450775, 9780504, 1795265022);

/// Return an integer x satisfying a^x = b (mod p)
#[inline]
pub fn mod_log(a: i64, b: i64, p: i64) -> Option<i64> {
    mod_log_with_lower_bound_constraint(a, b, p, 0)
}

/// Return an integer x satisfying a^x = b (mod p) and x >= lower
/// If no integers satisfy the condition, return None.
//      x = i * m + j (m = sqrt(p), 0 <= i,j <= m)
//          -> b = a^x
//               = a^(im+j)
//           a^j = b * (a^{-m})^i
//      So, we can pre-calculate a^{-m} and a^j (0 <= j <= m) and determine the existence of a^j for all i.
pub fn mod_log_with_lower_bound_constraint(a: i64, b: i64, p: i64, lower: i64) -> Option<i64> {
    let (a, b) = (a.rem_euclid(p), b.rem_euclid(p));

    // if p == 1, a = b = 0 (mod 1), so return 1.
    if p == 1 {
        return Some(lower);
    }
    // if b == 1, always a^0 = b = 1, so return 0.
    if b == 1 && lower <= 0 {
        return Some(0);
    }

    let ExtendedGcd { gcd, coef, neg: _ } = a.extended_gcd(p);
    let (g, inv) = (gcd, coef[0].rem_euclid(p));
    // if gcd(a, p) != 1, g = gcd(a, p), a = g * a', p = g * p'
    //      ->                (ga')^x = b (mod gp')
    //      ->            (ga')^x - b = gp' * k
    // so, b must also be a multiple of g.
    //  b = g * b'
    //      ->        (ga')^x - (gb') = gp'k
    //      -> ga'(ga')^(x-1) - (gb') = gp'k
    //      ->     a'(ga')^(x-1) - b' = p'k
    //  now, gcd(a', p') = 1. so, a'^{-1} (mod p') always exists.
    //      ->            (ga')^(x-1) = b'(a'^{-1}) (mod p')
    //      ->                a^(x-1) = b'(a'^{-1}) (mod p')
    if g != 1 {
        if b % g != 0 {
            return None;
        }
        let (na, nb, np) = (a / g, b / g, p / g);
        let inv = na.inverse_mod(np)?;
        let inv = inv.rem_euclid(np);
        return mod_log(a, nb * inv, np).map(|res| res + 1);
    }

    let m = (p as f64).sqrt().ceil() as i64;
    assert!(m * m >= p);
    let mut now = 1;
    // If there is no lower bound constraint, it is sufficient to have only the smallest index,
    // but if there is a lower bound constraint, there may be a constraint boundary, so all the indices are kept in Vec.
    let mut map = HashMap::new();
    for j in 0..m {
        map.entry(now).or_insert(vec![]).push(j);
        now = (now as i128 * a as i128 % p as i128) as i64;
    }

    let inv = inv.rem_euclid(p).pow_mod(m as u64, p);
    debug_assert_eq!((now as i128 * inv as i128).rem_euclid(p as i128), 1);

    let mut now = 1;
    for i in 0..=m {
        let r = (b as i128 * now as i128 % p as i128) as i64;

        if let Some(v) = map.get(&r) {
            for j in v {
                if i * m + j >= lower {
                    return Some(i * m + j);
                }
            }
        }

        now = (now as i128 * inv as i128 % p as i128) as i64;
    }

    None
}

/// Baby-step Giant-step Algorithm
/// If an integer i satisfying f^{i}(a) = b (mod p) is found, return i. If not, return None.
///     f(a: i64, i: i64) -> i64      : return an integer x satisfying f^{i}(a) = x (mod p)
///     f_inv(a: i64, i: i64) -> i64  : return an integer x satisfying f^{-i}(a) = x (mod p). Also, f_inv(f(a, 1), 1) = a is required.
pub fn baby_step_giant_step(
    a: i64,
    b: i64,
    p: i64,
    f: impl Fn(i64, i64) -> i64,
    f_inv: impl Fn(i64, i64) -> i64,
) -> Option<i64> {
    let m = (p as f64).sqrt().ceil() as i64;
    assert!(m * m >= p);

    let mut map = std::collections::HashMap::new();
    for j in 0..=m {
        let now = f(a, j);
        map.entry(now).or_insert(j);
    }

    let mut now = f_inv(b, 0);
    for i in 0..=m {
        if let Some(j) = map.get(&now) {
            return Some(i * m + j);
        }

        now = f_inv(now, m);
    }

    None
}

/// Return a minimum integer x (mod modulo) satisfying x = a[i] (mod p[i]) for any i and p[1]*p[2]*p[3].... (mod modulo)
///
/// Note: For any i, j (i != j), gcd(p[i], p[j]) MUST be 1.
//      x = t1 + t2p1 + t3p1p2 + t4p1p2p3 + ...
//          x  = a1 (mod p1)
//              -> a1 = x % p1 = t1 (mod p1)
//          x  = a2 (mod p2)
//              -> a2 = x % p2 = t1 + t2p1 (mod p2)
//              -> t2 = (a2 - t1) * p1^{-1} (mod p2)
//          ... so, t[k] = ((...((a[k] - t[1])p[1,k]^{-1} - t[2])p[2,k]^{-1} - ...)p[k-2,k]^{-1} - t[k-1]))p[k-1,k]^{-1} (mod p[k])
//                       = a[k]p[1,k]^{-1}p[2,k]^{-1}...p[k-1,k]^{-1} - t[1]p[1,k]^{-1}p[2,k]^{-1}...p[k-1,k]^{-1} - t[2]p[2,k]^{-1}p[3,k]^{-1}...p[k-1,k]^{-1} - ... - t[k-1]p[k-1,k]^{-1}
//                       = a[k](p[1,k]p[2,k]...p[k-1,k])^{-1} - t[1](p[1,k]p[2,k]...p[k-1,k])^{-1} - t[2](p[2,k]p[3,k]...p[k-1,k])^{-1} - ... - t[k-1]p[k-1,k]^{-1}
//                       = (a[k] - x[..k]) * (p[1,k]p[2,k]p[3,k]...p[k-1,k])^{-1}
//                       = (a[k] - res[k]) * prod[k]^{-1}
#[inline]
pub fn garner(a: &[i64], p: &[i64], modulo: i64) -> (i64, i64) {
    assert_eq!(a.len(), p.len());
    // prod[i] = p[0]p[1]...p[i-1]
    // res[i]  = t[0] + t[1]p[0] + t[2]p[0]p[1] + ... t[i-1]p[0]p[1]...p[i-2]
    let mut prod = vec![1; p.len() + 1];
    let mut res = vec![0; p.len() + 1];
    for (i, (&a, &m)) in a.iter().zip(p.iter()).enumerate() {
        let a = a % m;
        let inv = prod[i]
            .inverse_mod(m)
            .expect("math::garner : inverse_mod is not found");
        let t = ((a - res[i]) * inv).rem_euclid(m);
        for (i, &p) in p.iter().enumerate().skip(i + 1) {
            res[i] = (res[i] + (t * prod[i])) % p;
            prod[i] = (prod[i] * m) % p;
        }
        res[p.len()] = (res[p.len()] + (t * prod[p.len()])) % modulo;
        prod[p.len()] = (prod[p.len()] * m) % modulo;
    }
    (res[p.len()], prod[p.len()])
}

/// Return a minimum integer x (mod modulo) satisfying x = a[i] (mod p[i]) for any i and p[1]*p[2]*p[3].... (mod modulo)
/// For any i, j (i != j), gcd(p[i], p[j]) = 1 is not required.
/// If the condition is inconsistent and no solution exists, return None.
#[inline]
pub fn garner_prechecked(a: &[i64], p: &[i64], modulo: i64) -> Option<(i64, i64)> {
    let mut p = p.to_vec();
    for i in 0..a.len() {
        for j in 0..i {
            let mut g = p[i].gcd(p[j]);

            if (a[i] - a[j]) % g != 0 {
                return None;
            }

            (p[i], p[j]) = (p[i] / g, p[j] / g);

            let mut gi = p[i].gcd(g);
            let mut gj = g / gi;

            while {
                g = gi.gcd(gj);
                gi *= g;
                gj /= g;
                g != 1
            } {}

            (p[i], p[j]) = (p[i] * gi, p[j] * gj);
        }
    }

    Some(garner(a, &p, modulo))
}

/// Return xor bases for list `a`.
///
/// Return values are not in any specific order, so you need sort if necessary.
pub fn xor_base(a: &[u64]) -> Vec<u64> {
    let mut res = vec![];
    for &(mut a) in a {
        for &base in &res {
            a = a.min(a ^ base);
        }

        if a > 0 {
            res.push(a);
        }
    }

    res
}

/// Enumerate prime numbers using a linear sieve.
///
/// The constructor is const fn, so compile-time computation is possible.
///
/// MAX is exclusive. For example, MAX=10, think of it as enumerating the prime numbers "2..10", not "2..=10".
pub struct Sieve<const MAX: usize = 1000010> {
    count: usize,
    primes: [usize; MAX],
}

impl<const MAX: usize> Sieve<MAX> {
    pub const fn new() -> Self {
        let mut primes = [usize::MAX; MAX];
        let mut count = 0;

        let mut i = 2;
        while i < MAX {
            if primes[i] == usize::MAX {
                primes[i] = i;
                primes[count] = i;
                count += 1;
            }

            let mut j = 0;
            while j < count {
                if primes[j] > primes[i] || primes[j] * i >= MAX {
                    break;
                }
                primes[primes[j] * i] = primes[j];
                j += 1;
            }

            i += 1;
        }

        Self { count, primes }
    }

    pub const fn count(&self) -> usize {
        self.count
    }

    pub fn primes(&self) -> impl Iterator<Item = usize> + '_ {
        self.primes.iter().copied().take(self.count)
    }
}

impl Index<usize> for Sieve {
    type Output = usize;
    fn index(&self, index: usize) -> &Self::Output {
        &self.primes[index]
    }
}

/// Memory-saving and compact sieve.
///
/// It does not have information about prime factors, only whether a given natural number is prime or not.
pub struct CompactSieve {
    size: usize,
    block: Vec<u64>,
}

impl CompactSieve {
    const B: usize = u64::BITS as usize;
    const B2: usize = Self::B * 2;
    const T: usize = Self::B.trailing_zeros() as usize;
    const T2: usize = Self::T + 1;

    /// Construct a sieve in the range `0..size`.
    pub fn new(size: usize) -> Self {
        let len = (size + Self::B2 - 1) >> Self::T2;
        let mut block = vec![u64::MAX; len];
        let mut i = 3;
        while i < size {
            if block[i >> Self::T2] == 0 {
                i += Self::B2;
                continue;
            }

            if (block[i >> Self::T2] >> ((i >> 1) & (Self::B - 1))) & 1 != 0 {
                for j in (3..)
                    .step_by(2)
                    .map(|j| i * j)
                    .take_while(|&j| j < len << Self::T2)
                    .map(|j| j >> 1)
                {
                    block[j >> Self::T] &= !(1 << (j & (Self::B - 1)));
                }
            }

            i += 2;
        }

        Self { size, block }
    }

    /// Enumerate prime numbers in the range of `0..size`.
    ///
    /// # Examples
    /// ```rust
    /// use math::CompactSieve;
    ///
    /// let sieve = CompactSieve::new(50);
    /// assert_eq!(sieve.primes().collect::<Vec<_>>(), vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]);
    /// ```
    pub fn primes(&self) -> impl Iterator<Item = usize> + '_ {
        once(2)
            .chain(
                self.block
                    .iter()
                    .enumerate()
                    .flat_map(|(i, &b)| {
                        (0..Self::B).filter_map(move |j| {
                            ((b >> j) & 1 != 0).then_some(((j | (i << Self::T)) << 1) | 1)
                        })
                    })
                    .skip(1),
            )
            .take_while(|&p| p < self.size)
    }
}

#[cfg(test)]
mod tests {
    use rand::{thread_rng, Rng};

    use super::*;

    #[test]
    fn gcd_lcm_test() {
        assert_eq!(12u32.gcd(8), 4);
        assert_eq!(12u32.gcd(0), 12);
        assert_eq!(8u32.gcd(12), 4);
        assert_eq!(0u32.gcd(12), 12);

        assert_eq!(12u32.lcm(8), 24);
        assert_eq!(12u32.lcm(0), 0);
        assert_eq!(8u32.lcm(12), 24);
        assert_eq!(0u32.lcm(12), 0);

        assert_eq!(
            1_000_000_000_000_000_000u64.lcm(2_000_000_000_000_000_000),
            2_000_000_000_000_000_000
        );
    }

    #[test]
    fn ext_gcd_random_test() {
        let mut rng = thread_rng();
        for _ in 0..1000 {
            let a = rng.gen::<u32>();
            let b = rng.gen();

            let ExtendedGcd { gcd, coef, neg } = a.extended_gcd(b);
            let (mut ax, mut by) = (coef[0] as u64 * a as u64, coef[1] as u64 * b as u64);
            ax = if neg[0] { ax.wrapping_neg() } else { ax };
            by = if neg[1] { by.wrapping_neg() } else { by };
            assert_eq!(ax.wrapping_add(by), gcd as u64);
        }
    }

    #[test]
    fn crt_random_test() {
        let mut rng = thread_rng();
        for _ in 0..1000 {
            let m0 = rng.gen_range(1u32..=u32::MAX) as u64;
            let a = rng.gen_range(0..m0);
            let m1 = rng.gen_range(1u32..=u32::MAX) as u64;
            let b = rng.gen_range(0..m1);

            if let Some((res, lcm)) = a.crt(m0, b, m1) {
                assert_eq!(res % m0, a);
                assert_eq!(res % m1, b);
                assert_eq!(lcm, m0.lcm(m1));
                assert!(res < m0.lcm(m1));
            }
        }

        // small case
        for _ in 0..1000 {
            let m0 = rng.gen_range(1u8..=u8::MAX) as u16;
            let a = rng.gen_range(0..m0);
            let m1 = rng.gen_range(1u8..=u8::MAX) as u16;
            let b = rng.gen_range(0..m1);

            if let Some((res, lcm)) = a.crt(m0, b, m1) {
                assert_eq!(res % m0, a);
                assert_eq!(res % m1, b);
                assert_eq!(lcm, m0.lcm(m1));
                assert!(res < m0.lcm(m1));
            } else {
                assert!((0..m0.lcm(m1)).all(|i| i % m0 != a || i % m1 != b));
            }
        }
    }

    #[test]
    fn miller_rabin_test_test() {
        const MAX: u64 = 100_000;
        let mut p = vec![std::u64::MAX; MAX as usize];

        for i in 2..MAX {
            if p[i as usize] == std::u64::MAX {
                for j in (2..MAX).take_while(|j| i * *j < MAX) {
                    p[(i * j) as usize] = i;
                }
                assert!(i.is_prime());
            } else {
                assert!(!i.is_prime());
            }
        }
    }

    #[test]
    fn factorize_test() {
        let mut f = 115940u64
            .factorize()
            .flat_map(|(f, c)| (0..c).map(move |_| f))
            .collect::<Vec<_>>();
        f.sort();

        assert_eq!(f, vec![2, 2, 5, 11, 17, 31]);

        let f = 998244353u64.factorize().collect::<Vec<_>>();
        assert_eq!(f, vec![(998244353, 1)]);

        let mut f = 999381247093216751u64.factorize().collect::<Vec<_>>();
        f.sort();
        assert_eq!(f, vec![(999665081, 1), (999716071, 1)]);
    }

    #[test]
    fn divisors_enumeration_test() {
        let mut f = 12u32.divisors();
        f.sort();

        assert_eq!(f, vec![1, 2, 3, 4, 6, 12]);

        let mut f = 999381247093216751u64.divisors();
        f.sort();
        assert_eq!(f, vec![1, 999665081, 999716071, 999381247093216751]);
    }

    #[test]
    fn primitive_root_test() {
        assert_eq!(998244353u32.primitive_root(), 3);
    }
}
