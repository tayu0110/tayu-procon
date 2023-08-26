use arbitrary_montgomery_modint::ArbitraryMontgomeryModint;
use numeric::Integer;
use simple_rand::xor_shift;

//////////////////////////////////////////////////////////////////////////////////
// Define famous functions for integers
//////////////////////////////////////////////////////////////////////////////////

/// Return gcd(x, y).
#[inline]
pub fn gcd<T: Integer>(mut x: T, mut y: T) -> T {
    while y != T::zero() {
        let (nx, ny) = (y, x % y);
        x = nx;
        y = ny;
    }
    x
}

/// Return lcm(x, y).
#[inline]
pub fn lcm<T: Integer>(x: T, y: T) -> T { x / gcd(x, y) * y }

/// Solve the equation "ax + by = gcd(a, b)"
/// Return (gcd(a, b), x, y)
//  s * 1 + t * 0 = s    ...(1)  (sx = 1, sy = 0)
//  s * 0 + t * 1 = t    ...(2)  (tx = 0, ty = 1)
//       -> (1) - (2) * |s/t|
//       -> s * (sx - tx * |s/t|) + t * (sy - ty * |s/t|) = s % t
// Repeating this, the right-hand side becomes gcd(s, t)
//  s * tx + t * ty = gcd(s, t)
#[inline]
pub fn ext_gcd<T: Integer>(a: T, b: T) -> (T, T, T) {
    let (mut s, mut t) = (a, b);
    let (mut sx, mut tx) = (T::one(), T::zero());
    let (mut sy, mut ty) = (T::zero(), T::one());
    while s % t != T::zero() {
        let d = s / t;

        let u = s % t;
        let ux = sx - tx * d;
        let uy = sy - ty * d;
        s = t;
        sx = tx;
        sy = ty;
        t = u;
        tx = ux;
        ty = uy;
    }

    (t, tx, ty)
}

/// Using p as the modulus, calculate a^n.
#[inline]
pub fn mod_pow(a: i64, mut n: i64, p: i64) -> i64 {
    let mut res = 1;
    let mut pow = a;
    while n != 0 {
        if n & 1 != 0 {
            res = (res as i128 * pow as i128 % p as i128) as i64;
        }
        pow = (pow as i128 * pow as i128 % p as i128) as i64;
        n >>= 1;
    }
    res
}

/// Return an integer x satisfying a^x = b (mod p)
#[inline]
pub fn mod_log(a: i64, b: i64, p: i64) -> Option<i64> { mod_log_with_lower_bound_constraint(a, b, p, 0) }

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

    let (g, inv, _) = ext_gcd(a, p);
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
        let (_, inv, _) = ext_gcd(na, np);
        let inv = inv.rem_euclid(np);
        if let Some(res) = mod_log(a, nb * inv, np) {
            return Some(res + 1);
        } else {
            return None;
        }
    }

    let m = (p as f64).sqrt().ceil() as i64;
    assert!(m * m >= p);
    let mut now = 1;
    // If there is no lower bound constraint, it is sufficient to have only the smallest index,
    // but if there is a lower bound constraint, there may be a constraint boundary, so all the indices are kept in Vec.
    let mut map = std::collections::HashMap::new();
    for j in 0..m {
        map.entry(now).or_insert(vec![]).push(j);
        now = (now as i128 * a as i128 % p as i128) as i64;
    }

    let inv = mod_pow(inv.rem_euclid(p), m, p);
    debug_assert_eq!((now as i128 * inv as i128).rem_euclid(p as i128), 1);

    let mut now = 1;
    for i in 0..=m {
        let r = (b as i128 * now as i128 % p as i128) as i64;

        if let Some(v) = map.get(&r) {
            for j in v {
                if i * m + j < lower {
                    continue;
                }
                return Some(i * m + j);
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
pub fn baby_step_giant_step(a: i64, b: i64, p: i64, f: impl Fn(i64, i64) -> i64, f_inv: impl Fn(i64, i64) -> i64) -> Option<i64> {
    let m = (p as f64).sqrt().ceil() as i64;
    assert!(m * m >= p);

    let mut map = std::collections::HashMap::new();
    for j in 0..=m {
        let now = f(a, j);
        if !map.contains_key(&now) {
            map.insert(now, j);
        }
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

/// Return an integer x less than lcm(m1, m2) satisfying x = a (mod m1) and x = b (mod m2) and lcm(m1, m2).
/// If no integers satisfy the condition, return None.
//      m1 = gcd(m1, m2) * p,   m2 = gcd(m1, m2) * q
//          -> x = a (mod gcd(m1, m2)) && x = b (mod gcd(m1, m2))
//      m1 * k + m2 * l = gcd(m1, m2) = d
//          -> now, * s (= (b - a) / d)
//      s * m1 * k + s * m2 * l = b - a
//          -> a + s * m1 * k = b - s * m2 * l = x
//          -> x = a (mod m1) && x = b (mod m2)
#[inline]
pub fn chinese_remainder_theorem(mut a: i64, mut m1: i64, mut b: i64, mut m2: i64) -> Option<(i64, i64)> {
    if m1 < m2 {
        std::mem::swap(&mut a, &mut b);
        std::mem::swap(&mut m1, &mut m2);
    }
    let (a, b) = (a.rem_euclid(m1), b.rem_euclid(m2));
    if m1 % m2 == 0 {
        return if a % m2 != b { None } else { Some((a, m1)) };
    }

    let (d, k, _) = ext_gcd(m1, m2);
    let u1 = m2 / d;

    if a % d != b % d {
        return None;
    }

    let x = (b - a) / d % u1 * k % u1;
    let m = m1 * u1;
    let res = (a + x * m1).rem_euclid(m);
    Some((res, m))
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
        let (_, inv, _) = ext_gcd(prod[i], m);
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
            let mut g = gcd(p[i], p[j]);

            if (a[i] - a[j]) % g != 0 {
                return None;
            }

            p[i] /= g;
            p[j] /= g;

            let mut gi = gcd(p[i], g);
            let mut gj = g / gi;

            g = gcd(gi, gj);
            gi *= g;
            gj /= g;
            while g != 1 {
                g = gcd(gi, gj);
                gi *= g;
                gj /= g;
            }

            p[i] *= gi;
            p[j] *= gj;
        }
    }

    Some(garner(a, &p, modulo))
}

/// The given number is determined to be prime or not prime using the Miller-Rabin primality test.
pub fn miller_rabin_test(p: u64) -> bool {
    if p == 1 || p & 1 == 0 {
        return p == 2;
    }

    let s = (p - 1).trailing_zeros();
    let t = (p - 1) >> s;
    let mont_zero = ArbitraryMontgomeryModint::raw(0, p);
    let mont_one = mont_zero.one();
    let mont_neg_one = mont_zero - mont_one;

    vec![2, 325, 9375, 28178, 450775, 9780504, 1795265022].iter().map(|&a| a % p).filter(|&a| a != 0).all(|a| {
        let a = ArbitraryMontgomeryModint::from_same_mod_unchecked(a, mont_zero);
        let at = a.pow(t);
        // a^t = 1 (mod p) or a^t = -1 (mod p)
        if at == mont_one || at == mont_neg_one {
            return true;
        }

        // found i satisfying a^((2^i)*t) = -1 (mod p)
        (1..s)
            .scan(at, |at, _| {
                *at *= *at;
                Some(*at)
            })
            .any(|at| at == mont_neg_one)
    })
}

pub fn divisors_enumeration(n: u64) -> Vec<u64> {
    let mut f = factorize(n);
    f.sort();

    let mut t = vec![];
    for f in f {
        match t.last_mut() {
            Some((c, cnt)) if *c == f => *cnt += 1,
            _ => t.push((f, 1)),
        }
    }

    let mut res = vec![1];
    for (c, cnt) in t {
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

/// Returns the result of prime factorization of integer `n`.
pub fn factorize(mut n: u64) -> Vec<u64> {
    if n == 1 {
        return vec![];
    }

    let mut res = vec![2u64; n.trailing_zeros() as usize];
    n >>= n.trailing_zeros();

    while let Some(g) = pollard_rho(n) {
        while n % g == 0 {
            res.push(g);
            n /= g;
        }
    }

    if n > 1 {
        res.push(n);
    }

    res
}

/// Find non-trival prime factors of integer `n` by Pollard's rho algorithm.
///
/// If found, return this; If not found, return None.
fn pollard_rho(n: u64) -> Option<u64> {
    // 1 is trival prime factor. So return None.
    if n <= 1 {
        return None;
    }

    if n & 1 == 0 {
        return Some(2);
    }

    // If n is prime number, n has no divisors of ifself.
    // So return itself.
    if miller_rabin_test(n) {
        return Some(n);
    }

    let m = (n as f64).powf(0.125).round() as i64 + 1;
    let mont_zero = ArbitraryMontgomeryModint::raw(0, n);
    let mont_one = mont_zero.one();
    let mut g = 1;

    for c in (1..n).map(|c| ArbitraryMontgomeryModint::from_same_mod_unchecked(c, mont_zero)) {
        let mut y = mont_zero;
        let mut q = mont_one;

        'base: for r in (0..).map(|i| 1 << i) {
            let x = y;
            (r..=(3 * r) >> 2).for_each(|_| y = y * y + c);
            for k in (((3 * r) >> 2)..r).step_by(m as usize) {
                let ys = y;
                (0..std::cmp::min(m, r - k)).for_each(|_| {
                    y = y * y + c;
                    q *= x - y;
                });
                g = gcd(q.val() as i64, n as i64);
                if g != 1 {
                    if g == n as i64 {
                        y = ys * ys + c;
                        while gcd((x - y).val() as i64, n as i64) == 1 {
                            y = y * y + c;
                        }
                        g = gcd((x - y).val() as i64, n as i64);
                    }
                    break 'base;
                }
            }
        }

        if g != n as i64 {
            break;
        }
    }

    pollard_rho(g as u64)
}

/// Same processing as ```tonelli_shanks()```, but without the prime number determination of `p`.
///
/// It works correctly only when `p` is a prime number, but it is the user's responsibility to manage whether `p` is a prime number or not.
pub fn tonelli_shanks_unchecked(n: u64, p: u64) -> Option<u64> {
    // ArbitraryMontgomeryModint expects only odd number for p. So, the case that p is equal to 2 must be processed the top of this procedure.
    if p == 2 {
        let res = n & 1;
        assert_eq!(res * res % p, n);
        return Some(res);
    }
    type Modint = ArbitraryMontgomeryModint;
    let mn = Modint::new(n, p);
    if mn.rawval() == 0 {
        assert_eq!(0 * 0 % p, n);
        return Some(0);
    }

    let one = mn.one();
    if mn.pow((p - 1) >> 1).rawval() != one.rawval() {
        return None;
    }

    if p & 0b11 == 3 {
        let s = mn.pow((p + 1) >> 2).val();
        let t = p - s;
        return Some(s.min(t));
    }

    for b in xor_shift(381928476372819).map(|v| v % (p - 2) + 2) {
        let b = Modint::from_same_mod(b, mn);
        if b.pow((p - 1) >> 1).rawval() != one.rawval() {
            let q = (p - 1).trailing_zeros() as u64;
            let s = (p - 1) >> q;

            let mut x = mn.pow((s + 1) >> 1);
            let mut x2 = x * x;
            let mut b = b.pow(s);
            let mninv = mn.inv();

            let mut shift = 2;
            while x2 != mn {
                let diff = mninv * x2;
                if diff.pow(1 << (q - shift)).rawval() != one.rawval() {
                    x *= b;
                    b *= b;
                    x2 *= b;
                } else {
                    b *= b;
                }
                shift += 1;
            }
            return Some(x.val());
        }
    }

    unreachable!()
}

/// Return a square root of `n` on mod `p`.
/// If return value is not found, return `None`.
///
/// `p` must be a prime number.
pub fn tonelli_shanks(n: u64, p: u64) -> Option<u64> {
    assert!(miller_rabin_test(p));
    tonelli_shanks_unchecked(n, p)
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

#[cfg(test)]
mod tests {
    use crate::divisors_enumeration;

    use super::{chinese_remainder_theorem, ext_gcd, factorize, gcd, lcm, miller_rabin_test};

    #[test]
    fn numeric_test() {
        assert_eq!(gcd(12, 8), 4);
        assert_eq!(gcd(12, 0), 12);
        assert_eq!(gcd(8, 12), 4);
        assert_eq!(gcd(0, 12), 12);

        assert_eq!(lcm(12, 8), 24);
        assert_eq!(lcm(12, 0), 0);
        assert_eq!(lcm(8, 12), 24);
        assert_eq!(lcm(0, 12), 0);

        assert_eq!(lcm(1000_000_000_000_000_000i64, 2000_000_000_000_000_000i64), 2000_000_000_000_000_000i64);

        let (g, x, y) = ext_gcd(111, 30);

        assert_eq!(g, 3);
        assert_eq!(x, 3);
        assert_eq!(y, -11);

        let (x, l) = chinese_remainder_theorem(2, 3, 3, 5).unwrap();
        assert_eq!(x, 8);
        assert_eq!(l, 15);
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
                assert!(miller_rabin_test(i));
            } else {
                assert!(!miller_rabin_test(i));
            }
        }
    }

    #[test]
    fn factorize_test() {
        let mut f = factorize(115940);
        f.sort();

        assert_eq!(f, vec![2, 2, 5, 11, 17, 31]);

        let f = factorize(998244353);
        assert_eq!(f, vec![998244353]);

        let mut f = factorize(999381247093216751);
        f.sort();
        assert_eq!(f, vec![999665081, 999716071]);
    }

    #[test]
    fn divisors_enumeration_test() {
        let mut f = divisors_enumeration(12);
        f.sort();

        assert_eq!(f, vec![1, 2, 3, 4, 6, 12]);

        let mut f = divisors_enumeration(999381247093216751);
        f.sort();
        assert_eq!(f, vec![1, 999665081, 999716071, 999381247093216751]);
    }
}
