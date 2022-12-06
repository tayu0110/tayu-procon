use math::gcd;
use numeric::{Error, IntoFloat, Numeric, One, Zero};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};

//////////////////////////////////////////////////////////////////////////////////
// Implement Rational Number
//////////////////////////////////////////////////////////////////////////////////
/// Represent rational numbers.
/// The denominator is always retained as a positive number.
// numerator / denominator
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub struct Rational {
    numerator: i64,
    denominator: i64,
}

impl Rational {
    pub fn new(num: i64, den: i64) -> Self {
        if den == 0 {
            return Self { numerator: 1, denominator: 0 };
        } else if num == 0 {
            return Self { numerator: 0, denominator: 1 };
        }
        let g = gcd(num.abs(), den.abs());
        let num = if num / num.abs() == den / den.abs() { num.abs() } else { -num.abs() };
        Self {
            numerator: num / g,
            denominator: den.abs() / g,
        }
    }

    pub fn is_nan(&self) -> bool { self.denominator == 0 }

    pub fn abs(self) -> Self {
        Self {
            numerator: self.numerator.abs(),
            denominator: self.denominator,
        }
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

        Self::new(self.numerator * rhs.denominator + rhs.numerator * self.denominator, self.denominator * rhs.denominator)
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

        Self::new(self.numerator * rhs.numerator, self.denominator * rhs.denominator)
    }
}

impl Div for Rational {
    type Output = Rational;
    fn div(self, rhs: Self) -> Self::Output {
        assert!(!self.is_nan());

        self * Self {
            numerator: rhs.denominator,
            denominator: rhs.numerator,
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
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "({} / {})", self.numerator, self.denominator) }
}

impl std::fmt::Debug for Rational {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "({} / {})", self.numerator, self.denominator) }
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
impl One for Rational {
    fn one() -> Self { Self { numerator: 1, denominator: 1 } }
}

impl Zero for Rational {
    fn zero() -> Self { Self { numerator: 0, denominator: 1 } }
}

impl Numeric for Rational {
    fn max_value() -> Self {
        Self {
            numerator: i64::max_value(),
            denominator: 1,
        }
    }
    fn min_value() -> Self {
        Self {
            numerator: i64::min_value(),
            denominator: 1,
        }
    }
}

impl IntoFloat for Rational {
    fn as_f64(self) -> f64 { self.try_into().unwrap() }
    fn as_f32(self) -> f32 { self.try_into().unwrap() }
}

impl<T: Into<i64>> From<T> for Rational {
    fn from(from: T) -> Self {
        Self {
            numerator: from.into(),
            denominator: 1,
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
