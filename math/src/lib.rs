use modint::MontgomeryOperator;
use numeric::integer::Integer;

//////////////////////////////////////////////////////////////////////////////////
// Define famous functions for integers
//////////////////////////////////////////////////////////////////////////////////

/// Return gcd(x, y).
pub fn gcd<T: Integer>(x: T, y: T) -> T {
    if y == T::zero() {
        x
    } else {
        gcd(y, x % y)
    }
}

/// Return lcm(x, y).
pub fn lcm<T: Integer>(x: T, y: T) -> T {
    x / gcd(x, y) * y
}

/// Solve the equation "ax + by = gcd(a, b)".
// ax + by = gcd(a, b)
// bx' + (a % b)y' = gcd(a, b)
//      if a % b == 0
//          b  = gcd(a, b)
//          && bx' = gcd(a, b) -> x' = 1, y' = 0;
//      else
//          bx' + (a - b * floor(a / b))y' = gcd(a, b)
//          ay' - b(x' - floor(a / b)y')    = gcd(a, b)
//              -> x = 'y, y = 'x - floor(a / b)'y
pub fn ext_gcd<T: Integer>(a: T, x: &mut T, b: T, y: &mut T) -> T {
    if b == T::zero() {
        *x = T::one();
        *y = T::zero();
        return a;
    }

    let g = ext_gcd(b, y, a % b, x);
    *y -= a / b * *x;
    g
}

/// Using p as the modulus, calculate a^n.
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

/// The given number is determined to be prime or not prime using the Miller-Rabin primality test.
pub fn miller_rabin_test(p: u64) -> bool {
    if p == 1 || p & 1 == 0 {
        return p == 2;
    }

    let s = (p - 1).trailing_zeros();
    let t = (p - 1) >> s;
    let mont = MontgomeryOperator::new(p as u64);

    vec![2, 325, 9375, 28178, 450775, 9780504, 1795265022]
        .iter()
        .filter(|a| *a % p != 0)
        .all(|a| {
            let a = if *a < p { *a } else { *a % p };
            let at = mont.pow(mont.ar(a as u64), t as u64);
            // a^t = 1 (mod p) or a^t = -1 (mod p)
            if at == mont.r || at == mont.neg_r {
                return true;
            }

            (1..s)
                .scan(at, |at, _| {
                    *at = mont.mul(*at, *at);
                    Some(*at)
                })
                .any(|at|
            // found i satisfying a^((2^i)*t) = -1 (mod p)
            at == mont.neg_r)
        })
}

/// Returns the result of prime factorization of integer n.
pub fn factorize(mut n: u64) -> Vec<u64> {
    if n == 1 {
        return vec![];
    }

    let mut res = if n & 1 == 0 {
        let tz = n.trailing_zeros();
        n >>= tz;
        (0..tz).map(|_| 2).collect()
    } else {
        vec![]
    };

    while let Some(g) = pollard_rho(n) {
        res.push(g);
        n /= g;
    }

    if n != 1 {
        res.push(n);
    }

    res
}

/// Find non-trival prime factors of integer n by Pollard's rho algorithm.
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
    // So return None.
    if miller_rabin_test(n) {
        return None;
    }

    let m = (n as f64).powf(0.125).round() as i64 + 1;
    let mont = MontgomeryOperator::new(n);
    let mut res_g = 0;

    for c in 1..n {
        let f = |ar| mont.add(mont.mul(ar, ar), c);
        let mut x = 0;
        let (mut y, mut ys) = (mont.mr(0), 0);
        let (mut g, mut q, mut r) = (1, 1, 1);
        let mut k = 0;

        while g == 1 {
            x = y;
            while k < (3 * r) >> 2 {
                y = f(mont.mr(y));
                k += 1;
            }
            while k < r && g == 1 {
                ys = y;
                for _ in 0..std::cmp::min(m, r - k) {
                    y = f(mont.mr(y));
                    q = mont.mul(
                        mont.mr(q),
                        mont.mr(std::cmp::max(x, y) - std::cmp::min(x, y)),
                    );
                }
                g = gcd(q as i64, n as i64);
                k += m;
            }
            k = r;
            r <<= 1;
        }
        if g == n as i64 {
            g = 1;
            y = ys;
            while g == 1 {
                y = f(mont.mr(y));
                g = gcd(
                    std::cmp::max(x, y) as i64 - std::cmp::min(x, y) as i64,
                    n as i64,
                );
            }
        }
        if g == n as i64 {
            continue;
        }

        res_g = g;
        break;
    }

    if miller_rabin_test(res_g as u64) {
        return Some(res_g as u64);
    }
    if miller_rabin_test(n / res_g as u64) {
        return Some(n / res_g as u64);
    }

    pollard_rho(res_g as u64)
}

#[cfg(test)]
mod tests {
    use super::{ext_gcd, factorize, gcd, lcm, miller_rabin_test};

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

        assert_eq!(
            lcm(1000_000_000_000_000_000i64, 2000_000_000_000_000_000i64),
            2000_000_000_000_000_000i64
        );

        let (mut x, mut y) = (0, 0);
        let g = ext_gcd(111, &mut x, 30, &mut y);

        assert_eq!(g, 3);
        assert_eq!(x, 3);
        assert_eq!(y, -11);
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
}
