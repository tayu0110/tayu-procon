// use tayu_procon::{
//     scan,
//     numeric::factorize
// };

#![allow(dead_code)]

use numeric::factorize;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(q: usize, a: [u64; q]);

    for a in a {
        let mut f = factorize(a);
        f.sort();

        write!(out, "{}", f.len()).unwrap();
        for f in f {
            write!(out, " {}", f).unwrap();
        }
        writeln!(out, "").unwrap();
    }
}

mod iolib {
use std::cell::RefCell;
use std::io::{
    Read, BufRead,
    Error
};
use std::str::SplitWhitespace;
use std::thread_local;

thread_local! {
    static BUF_SPLIT_WHITESPACE: RefCell<SplitWhitespace<'static>> = RefCell::new("".split_whitespace());
}

#[inline]
fn refill_buffer(interactive: bool) -> Result<(), Error> {
    let mut s = String::new();
    
    if cfg!(debug_assertions) || interactive {
        std::io::stdin().lock().read_line(&mut s)?;
    } else {
        std::io::stdin().lock().read_to_string(&mut s)?;
    }

    BUF_SPLIT_WHITESPACE.with(|buf_str| {
        *buf_str.borrow_mut() = Box::leak(s.into_boxed_str()).split_whitespace();
        Ok(())
    })
}

#[inline]
pub fn scan_string(interactive: bool) -> &'static str {
    BUF_SPLIT_WHITESPACE.with(|buf_str| {
        if let Some(s) = buf_str.borrow_mut().next() {
            return s;
        }

        refill_buffer(interactive).unwrap();

        if let Some(s) = buf_str.borrow_mut().next() {
            return s;
        }

        unreachable!("Read Error: No input items.");
    })
}

#[macro_export]
macro_rules! scan {
    // Terminator
    ( @interactive : $interactive:literal ) => {};
    // Terminator
    ( @interactive : $interactive:literal, ) => {};
    // Vec<Vec<....>>
    ( @interactive : $interactive:literal, $v: ident : [ [ $( $inner:tt )+ ] ; $len:expr ]) => {
        let $v = {
            let len = $len;
            (0..len).fold(vec![], |mut v, _| {
                $crate::scan!(@interactive: $interactive, w: [ $( $inner )+ ]);
                v.push(w);
                v
            })
        };
    };
    // Vec<Vec<....>>, ......
    ( @interactive : $interactive:literal, $v: ident : [ [ $( $inner:tt )+ ] ; $len:expr ] , $( $rest:tt )* ) => {
        $crate::scan!(@interactive: $interactive, [ [ $( $inner )+ ] ; $len ]);
        $crate::scan!(@interactive: $interactive, $( $rest )*);
    };
    // Vec<$t>
    ( @interactive : $interactive:literal, $v:ident : [ $t:tt ; $len:expr ]) => {
        let $v = {
            let len = $len;
            (0..len).map(|_| { $crate::scan!(@interactive: $interactive, $v : $t); $v }).collect::<Vec<_>>()
        };
    };
    // Vec<$t>, .....
    ( @interactive : $interactive:literal, $v:ident : [ $t:tt ; $len:expr ] , $( $rest:tt )* ) => {
        let $v = {
            let len = $len;
            (0..len).map(|_| { $crate::scan!(@interactive: $interactive, $v : $t); $v }).collect::<Vec<_>>()
        };
        $crate::scan!(@interactive: $interactive, $( $rest )*);
    };
    // Expand tuple
    ( @interactive : $interactive:literal, @expandtuple, ( $t:tt )) => {
        { let tmp = $crate::iolib::scan_string($interactive).parse::<$t>().unwrap(); tmp }
    };
    // Expand tuple
    ( @interactive : $interactive:literal, @expandtuple, ( $t:tt $( , $rest:tt )* ) ) => {
        (
            $crate::scan!(@interactive: $interactive, @expandtuple, ( $t )),
            $( $crate::scan!(@interactive: $interactive, @expandtuple, ( $rest )), )*
        )
    };
    // let $v: ($t, $u, ....) = (.......)
    ( @interactive : $interactive:literal, $v:ident : ( $( $rest:tt )* ) ) => {
        let $v = $crate::scan!(@interactive: $interactive, @expandtuple, ( $( $rest )* ));
    };
    // let $v: $t = ......
    ( @interactive : $interactive:literal, $v:ident : $t:ty ) => {
        let $v = $crate::iolib::scan_string($interactive).parse::<$t>().unwrap();
    };
    // let $v: $t = ......, .......
    ( @interactive : $interactive:literal, $v:ident : $t:ty, $( $rest:tt )+ ) => {
        $crate::scan!(@interactive: $interactive, $v : $t);
        $crate::scan!(@interactive: $interactive, $( $rest )+);
    };
    // ......
    ( $( $rest:tt )* ) => {
        $crate::scan!(@interactive: false, $( $rest )*);
    };
}

#[macro_export]
macro_rules! scani {
    ( $( $rest:tt )* ) => {
        $crate::scan!(@interactive: true, $( $rest )*);
    };
}
}

mod numeric {
    use std::ops::{
        Add, Sub, Mul, Div, Rem, Neg,
        AddAssign, SubAssign, MulAssign, DivAssign, RemAssign,
        Shl, Shr,
        ShlAssign, ShrAssign
    };
    
    #[derive(Debug)]
    pub struct Error(&'static str);
    
    impl std::fmt::Display for Error {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "{}", self.0)
        }
    }
    
    impl std::error::Error for Error { }
    
    pub trait Numeric
            : Add<Self, Output = Self> + Sub<Self, Output = Self> + Mul<Self, Output = Self> + Div<Self, Output = Self> + Neg<Output = Self> 
                + AddAssign + SubAssign + MulAssign + DivAssign
                + std::fmt::Debug + std::fmt::Display + Clone + Copy + PartialEq + PartialOrd + Default {
        fn one() -> Self;
        fn zero() -> Self;
        fn max_value() -> Self;
        fn min_value() -> Self;
        fn abs(self) -> Self;
    }
    
    pub trait Integer
            : Numeric + Rem<Self, Output = Self> + RemAssign
              + Shl<Self, Output = Self> + Shr<Self, Output = Self> + ShlAssign + ShrAssign
              + std::hash::Hash + Eq + Ord {
    }
    
    pub trait IntoFloat : Numeric {
        fn as_f64(self) -> f64;
        fn as_f32(self) -> f32;
    }
    
    //////////////////////////////////////////////////////////////////////////////////
    // Implement Numeric, Integer and IntoFloat for i64
    //////////////////////////////////////////////////////////////////////////////////
    impl Numeric for i64 {
        fn one() -> Self { 1 }
        fn zero() -> Self { 0 }
        fn max_value() -> Self { std::i64::MAX }
        fn min_value() -> Self { std::i64::MIN }
        fn abs(self) -> Self { self.abs() }
    }
    impl Integer for i64 {
    }
    impl IntoFloat for i64 {
        fn as_f64(self) -> f64 {
            self as f64
        }
        fn as_f32(self) -> f32 {
            self as f32
        }
    }

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
    
    use crate::modint::MontgomeryOperator;

    /// The given number is determined to be prime or not prime using the Miller-Rabin primality test.
    pub fn miller_rabin_test(p: u64) -> bool {
        if p == 1 || p & 1 == 0 {
            return p == 2;
        }

        let s = (p-1).trailing_zeros();
        let t = (p-1) >> s;
        let mont = MontgomeryOperator::new(p as u64);

        vec![2, 325, 9375, 28178, 450775, 9780504, 1795265022].iter().filter(|a| *a % p != 0).all(|a| {
            let a = if *a < p { *a } else { *a % p };
            // let at = mod_pow(*a, t, p);
            let at = mont.pow(mont.ar(a as u64), t as u64);
            // a^t = 1 (mod p) or a^t = -1 (mod p)
            // if at == 1 || at == p-1 {
            //     return true;
            // }
            if at == mont.r || at == mont.neg_r {
                return true;
            }

            (1..s).scan(at, |at, _| {
                // *at = (*at as i128 * *at as i128 % p as i128) as i64;
                *at = mont.mul(*at, *at);
                Some(*at)
            }).any(|at|
                // found i satisfying a^((2^i)*t) = -1 (mod p)
                // at == p-1
                at == mont.neg_r
            )
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
                    for _ in 0..std::cmp::min(m, r-k) {
                        y = f(mont.mr(y));
                        q = mont.mul(mont.mr(q), mont.mr(std::cmp::max(x, y) - std::cmp::min(x, y)));
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
                    g = gcd(std::cmp::max(x, y) as i64 - std::cmp::min(x, y) as i64, n as i64);
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
}

mod modint {
    pub struct MontgomeryOperator {
        pub modulo: u64,
        pub inv_modulo: u64,
        pub r: u64,
        pub neg_r: u64,
        pub half_modulo: u64,
        pub r2: u64,
        pub d: u64
    }
    
    impl MontgomeryOperator {
        pub const fn new(modulo: u64) -> Self {
            assert!(modulo & 1 != 0);
    
            let inv_modulo = {
                let mut i = 0;
                let mut inv_modulo = modulo;
                while i < 5 {
                    inv_modulo = inv_modulo.wrapping_mul(2u64.wrapping_sub(modulo.wrapping_mul(inv_modulo)));
                    i += 1;
                }
                inv_modulo
            };
    
            let half_modulo = (modulo >> 1) + 1;
            let r = modulo.wrapping_neg() % modulo;
            let neg_r = modulo - r;
            let r2 = ((modulo as u128).wrapping_neg() % (modulo as u128)) as u64;
            let d = (modulo-1) >> (modulo-1).trailing_zeros();
    
            Self { modulo, inv_modulo, r, neg_r, half_modulo, r2, d }
        }
    
        pub const fn add(&self, a: u64, b: u64) -> u64 {
            let (t, fa) = a.overflowing_add(b);
            let (u, fs) = t.overflowing_sub(self.modulo);
            if fa || !fs { u } else { t }
        }
    
        pub const fn sub(&self, a: u64, b: u64) -> u64 {
            let (t, f) = a.overflowing_sub(b);
            if f { t.wrapping_add(self.modulo) } else { t }
        }
    
        pub const fn div2(&self, ar: u64) -> u64 {
            if ar & 1 != 0 {
                (ar >> 1) + self.half_modulo
            } else {
                ar >> 1
            }
        }
    
        pub const fn mul(&self, ar: u64, br: u64) -> u64 {
            let t = (ar as u128) * (br as u128);
            let (t, f) = ((t >> 64) as u64).overflowing_sub((((((t as u64).wrapping_mul(self.inv_modulo)) as u128) * self.modulo as u128) >> 64) as u64);
            if f { t.wrapping_add(self.modulo) } else { t }
        }
    
        pub const fn mr(&self, ar: u64) -> u64 {
            let (t, f) = (((((ar.wrapping_mul(self.inv_modulo)) as u128) * (self.modulo as u128)) >> 64) as u64).overflowing_neg();
            if f { t.wrapping_add(self.modulo) } else { t }
        }
        pub const fn ar(&self, a: u64) -> u64 {
            self.mul(a, self.r2)
        }
    
        pub const fn pow(&self, mut ar: u64, mut b: u64) -> u64 {
            let mut t = if (b & 1) != 0 { ar } else { self.r };
            b >>= 1;
            while b != 0 {
                ar = self.mul(ar, ar);
                if b & 1 != 0 { t = self.mul(t, ar); }
                b >>= 1;
            }
            t
        }
    }
}
