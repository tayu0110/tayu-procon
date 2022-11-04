/////////////////////////////////////////////////////////////////////////////
/// 
/// Complex Number
///
/////////////////////////////////////////////////////////////////////////////

use std::ops::{
    Add, Sub, Mul, Div,
};
use numeric::float::Float;

pub struct Complex<T: Float = f64> {
    re: T,
    im: T
}

impl<T: Float> Complex<T> {
    pub const fn new(re: T, im: T) -> Self {
        Self { re, im }
    }

    pub fn norm_sq(&self) -> T {
        self.re * self.re + self.im * self.im
    }

    pub fn norm(&self) -> T {
        self.norm_sq().sqrt()
    }

    pub fn arg(&self) -> T {
        self.im.atan2(self.re)
    }

    pub fn from_polar(norm: T, arg: T) -> Self {
        Self { re: norm * arg.cos(), im: norm * arg.sin() }
    }

    pub fn to_polar(&self) -> PolarFormComplex<T> {
        PolarFormComplex::new(self.norm(), self.arg())
    }
}

impl<T: Float> Add for Complex<T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.re + rhs.re, self.im + rhs.im)
    }
}

impl<T: Float> Sub for Complex<T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(self.re - rhs.re, self.im - rhs.im)
    }
}

impl<T: Float> Mul for Complex<T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.re * rhs.re - self.im * rhs.im, self.re * rhs.im + self.im * rhs.re)
    }
}

impl<T: Float> Div for Complex<T> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        let c = self * Self::new(rhs.re, -rhs.re);
        let norm2 = rhs.re * rhs.re + rhs.im * rhs.im;
        Self::new(c.re / norm2, c.im / norm2)
    }
}

pub struct PolarFormComplex<T: Float = f64> {
    norm: T,
    arg: T
}

impl<T: Float> PolarFormComplex<T> {
    pub const fn new(norm: T, arg: T) -> Self {
        Self { norm, arg }
    }
}

impl<T: Float> Mul for PolarFormComplex<T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.norm * rhs.norm, self.arg + rhs.arg)
    }
}

impl<T: Float> Div for PolarFormComplex<T> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        Self::new(self.norm / rhs.norm, self.arg - rhs.arg)
    }
}
