pub mod float;
pub mod integer;
pub mod signed;

pub use float::Float;
pub use integer::Integer;
pub use signed::Signed;
pub use zero_one::{One, Zero};

use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

#[derive(Debug)]
pub struct Error(pub &'static str);

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl std::error::Error for Error {}

pub trait UnorderedNumeric:
    Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Mul<Self, Output = Self>
    + Div<Self, Output = Self>
    + AddAssign
    + SubAssign
    + MulAssign
    + DivAssign
    + std::fmt::Debug
    + std::fmt::Display
    + Clone
    + Copy
    + PartialEq
    + Default
    + Zero
    + One
{
}

pub trait Numeric:
    Add<Self, Output = Self>
    + Sub<Self, Output = Self>
    + Mul<Self, Output = Self>
    + Div<Self, Output = Self>
    + AddAssign
    + SubAssign
    + MulAssign
    + DivAssign
    + std::fmt::Debug
    + std::fmt::Display
    + Clone
    + Copy
    + PartialEq
    + PartialOrd
    + Default
    + Zero
    + One
{
    fn max_value() -> Self;
    fn min_value() -> Self;
}

pub trait IntoFloat: Numeric {
    fn as_f64(self) -> f64;
    fn as_f32(self) -> f32;
}

impl IntoFloat for i64 {
    fn as_f64(self) -> f64 {
        self as f64
    }
    fn as_f32(self) -> f32 {
        self as f32
    }
}
