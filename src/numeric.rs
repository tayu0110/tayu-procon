use std::ops::{
    Add, Sub, Mul, Div, Rem, Neg,
    AddAssign, SubAssign, MulAssign, DivAssign, RemAssign,
    Shl, Shr,
    ShlAssign, ShrAssign
};
use std::convert::{
    From, Into,
    TryInto
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
          + Shl + Shr + ShlAssign + ShrAssign
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
// Implement Rational Number
//////////////////////////////////////////////////////////////////////////////////
/// Represent rational numbers.
/// The denominator is always retained as a positive number.
// numerator / denominator
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Rational {
    numerator: i64,
    denominator: i64
}

impl Rational {
    pub fn new(num: i64, den: i64) -> Self {
        if den == 0 {
            return Self {
                numerator: 1,
                denominator: 0
            };
        } else if num == 0 {
            return Self {
                numerator: 0,
                denominator: 1
            };
        }
        let g = gcd(num.abs(), den.abs());
        let num = if num / num.abs() == den / den.abs() {
            num.abs()
        } else {
            -num.abs()
        };
        Self {
            numerator: num / g,
            denominator: den.abs() / g
        }
    }

    pub fn is_nan(&self) -> bool {
        self.denominator == 0
    }
}

impl Neg for Rational {
    type Output = Rational;
    fn neg(self) -> Self::Output {
        assert!(!self.is_nan());
        
        Self::new(-self.numerator, self.denominator)
    }
}

//////////////////////////////////////////////////////////////////////////////////
// Define operations on rational numbers
//////////////////////////////////////////////////////////////////////////////////
impl Add for Rational {
    type Output = Rational;
    fn add(self, rhs: Self) -> Self::Output {
        assert!(!self.is_nan());

        Self::new(
            self.numerator * rhs.denominator + rhs.numerator * self.denominator,
            self.denominator * rhs.denominator)
    }
}

impl Sub for Rational {
    type Output = Rational;
    fn sub(self, rhs: Self) -> Self::Output {
        assert!(!self.is_nan());

        self + (-rhs)
    }
}

impl Mul for Rational {
    type Output = Rational;
    fn mul(self, rhs: Self) -> Self::Output {
        assert!(!self.is_nan());
        
        Self::new(
            self.numerator * rhs.numerator,
            self.denominator * rhs.denominator)
    }
}

impl Div for Rational {
    type Output = Rational;
    fn div(self, rhs: Self) -> Self::Output {
        assert!(!self.is_nan());
        
        self * Self {
            numerator: rhs.denominator,
            denominator: rhs.numerator
        }
    }
}

impl AddAssign for Rational {
    fn add_assign(&mut self, rhs: Self) {
        assert!(!self.is_nan());
    
        *self = self.clone() + rhs;
    }
}

impl SubAssign for Rational {
    fn sub_assign(&mut self, rhs: Self) {
        assert!(!self.is_nan());
    
        *self = self.clone() - rhs;
    }
}

impl MulAssign for Rational {
    fn mul_assign(&mut self, rhs: Self) {
        assert!(!self.is_nan());
    
        *self = self.clone() * rhs;
    }
}

impl DivAssign for Rational {
    fn div_assign(&mut self, rhs: Self) {
        assert!(!self.is_nan());
    
        *self = self.clone() / rhs;
    }
}

impl std::fmt::Display for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} / {})", self.numerator, self.denominator)
    }
}

impl std::fmt::Debug for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({} / {})", self.numerator, self.denominator)
    }
}


//////////////////////////////////////////////////////////////////////////////////
// Define operations between rational numbers and floating point numbers.
//////////////////////////////////////////////////////////////////////////////////
impl Add<f64> for Rational {
    type Output = f64;
    fn add(self, rhs: f64) -> Self::Output {
        let lhs: f64 = self.try_into().unwrap();
        lhs + rhs
    }
}

impl Sub<f64> for Rational {
    type Output = f64;
    fn sub(self, rhs: f64) -> Self::Output {
        let lhs: f64 = self.try_into().unwrap();
        lhs - rhs
    }
}

impl Mul<f64> for Rational {
    type Output = f64;
    fn mul(self, rhs: f64) -> Self::Output {
        let lhs: f64 = self.try_into().unwrap();
        lhs * rhs
    }
}

impl Div<f64> for Rational {
    type Output = f64;
    fn div(self, rhs: f64) -> Self::Output {
        let lhs: f64 = self.try_into().unwrap();
        lhs / rhs
    }
}

//////////////////////////////////////////////////////////////////////////////////
// Implement Numeric and IntoFloat for Rational
//////////////////////////////////////////////////////////////////////////////////
impl Numeric for Rational {
    fn one() -> Self {
        Self {
            numerator: 1,
            denominator: 1
        }
    }
    fn zero() -> Self {
        Self {
            numerator: 0,
            denominator: 1
        }
    }
    fn max_value() -> Self {
        Self {
            numerator: i64::max_value(),
            denominator: 1
        }
    }
    fn min_value() -> Self {
        Self {
            numerator: i64::min_value(),
            denominator: 1
        }
    }
    fn abs(self) -> Self {
        Self {
            numerator: self.numerator.abs(),
            denominator: self.denominator
        }
    }
}

impl IntoFloat for Rational {
    fn as_f64(self) -> f64 {
        self.try_into().unwrap()
    }
    fn as_f32(self) -> f32 {
        self.try_into().unwrap()
    }
}

impl<T: Into<i64>> From<T> for Rational {
    fn from(from: T) -> Self {
        Self {
            numerator: from.into(),
            denominator: 1
        }
    }
}

impl TryInto<f64> for Rational {
    type Error = Error;
    fn try_into(self) -> Result<f64, Self::Error> {
        if self.is_nan() {
            Err(Error("Failed to convert into f64 because this is NaN."))
        } else {
            Ok(self.numerator as f64 / self.denominator as f64)
        }
    }
}

impl TryInto<f32> for Rational {
    type Error = Error;
    fn try_into(self) -> Result<f32, Self::Error> {
        if self.is_nan() {
            Err(Error("Failed to convert into f32 because this is NaN."))
        } else {
            Ok(self.numerator as f32 / self.denominator as f32)
        }
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


#[cfg(test)]
mod tests {
    use super::{
        gcd, lcm, ext_gcd
    };

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

        assert_eq!(lcm(1000_000_000_000_000_000, 2000_000_000_000_000_000), 2000_000_000_000_000_000);

        let (mut x, mut y) = (0, 0);
        let g = ext_gcd(111, &mut x, 30, &mut y);

        assert_eq!(g, 3);
        assert_eq!(x, 3);
        assert_eq!(y, -11);
    }
}