/////////////////////////////////////////////////////////////////////////////
/// 
/// Complex Number
///
/////////////////////////////////////////////////////////////////////////////

use std::ops::{
    Add, Sub, Mul, Div,
    AddAssign, SubAssign, MulAssign, DivAssign
};
use std::convert::From;
use numeric::float::Float;

#[derive(Clone, Copy, PartialEq, PartialOrd)]
pub struct Complex<T: Float = f64> {
    re: T,
    im: T
}

impl<T: Float> Complex<T> {
    pub fn new(re: T, im: T) -> Self {
        Self { re, im }
    }

    pub fn real(&self) -> T {
        self.re
    }

    pub fn imag(&self) -> T {
        self.im
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

    pub fn conjugate(&self) -> Self {
        Self { re: self.re, im: -self.im }
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
        let c = self * Self::new(rhs.re, -rhs.im);
        let norm2 = rhs.re * rhs.re + rhs.im * rhs.im;
        Self::new(c.re / norm2, c.im / norm2)
    }
}

impl Add<f64> for Complex<f64> {
    type Output = Complex<f64>;
    fn add(self, rhs: f64) -> Self::Output {
        Self::new(self.real() + rhs, self.imag())
    }
}

impl Sub<f64> for Complex<f64> {
    type Output = Complex<f64>;
    fn sub(self, rhs: f64) -> Self::Output {
        Self::new(self.real() - rhs, self.imag())
    }
}

impl Mul<f64> for Complex<f64> {
    type Output = Complex<f64>;
    fn mul(self, rhs: f64) -> Self::Output {
        Self::new(self.real() * rhs, self.imag() * rhs)
    }
}

impl Div<f64> for Complex<f64> {
    type Output = Complex<f64>;
    fn div(self, rhs: f64) -> Self::Output {
        Self::new(self.real() / rhs, self.imag() / rhs)
    }
}

impl Add<f32> for Complex<f32> {
    type Output = Complex<f32>;
    fn add(self, rhs: f32) -> Self::Output {
        Self::new(self.real() + rhs, self.imag())
    }
}

impl Sub<f32> for Complex<f32> {
    type Output = Complex<f32>;
    fn sub(self, rhs: f32) -> Self::Output {
        Self::new(self.real() - rhs, self.imag())
    }
}

impl Mul<f32> for Complex<f32> {
    type Output = Complex<f32>;
    fn mul(self, rhs: f32) -> Self::Output {
        Self::new(self.real() * rhs, self.imag() * rhs)
    }
}

impl Div<f32> for Complex<f32> {
    type Output = Complex<f32>;
    fn div(self, rhs: f32) -> Self::Output {
        Self::new(self.real() / rhs, self.imag() / rhs)
    }
}

impl<T: Float> AddAssign for Complex<T> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<T: Float> SubAssign for Complex<T> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<T: Float> MulAssign for Complex<T> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<T: Float> DivAssign for Complex<T> {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl<T: Float> From<T> for Complex<T> {
    fn from(from: T) -> Self {
        Self::new(from, T::zero())
    }
}

impl AddAssign<f64> for Complex<f64> {
    fn add_assign(&mut self, rhs: f64) {
        self.re += rhs;
    }
}

impl SubAssign<f64> for Complex<f64> {
    fn sub_assign(&mut self, rhs: f64) {
        self.re -= rhs;
    }
}

impl MulAssign<f64> for Complex<f64> {
    fn mul_assign(&mut self, rhs: f64) {
        self.re *= rhs;
        self.im *= rhs;
    }
}

impl DivAssign<f64> for Complex<f64> {
    fn div_assign(&mut self, rhs: f64) {
        self.re /= rhs;
        self.im /= rhs;
    }
}

impl AddAssign<f32> for Complex<f32> {
    fn add_assign(&mut self, rhs: f32) {
        self.re += rhs;
    }
}

impl SubAssign<f32> for Complex<f32> {
    fn sub_assign(&mut self, rhs: f32) {
        self.re -= rhs;
    }
}

impl MulAssign<f32> for Complex<f32> {
    fn mul_assign(&mut self, rhs: f32) {
        self.re *= rhs;
        self.im *= rhs;
    }
}

impl DivAssign<f32> for Complex<f32> {
    fn div_assign(&mut self, rhs: f32) {
        self.re /= rhs;
        self.im /= rhs;
    }
}

impl std::fmt::Debug for Complex<f64> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("{}", self.real());
        if self.imag().abs() > 1e-20 {
            s += format!("{:+}i", self.imag()).as_str();
        }
        write!(f, "{}", s)
    }
}


//////////////////////////////////////////////////////////
/// Polar Form Complex
//////////////////////////////////////////////////////////
pub struct PolarFormComplex<T: Float = f64> {
    norm: T,
    arg: T
}

impl<T: Float> PolarFormComplex<T> {
    pub fn new(norm: T, arg: T) -> Self {
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


#[cfg(test)]
mod tests {
    use super::{
        Complex
    };

    fn abs_diff(a: &Complex, b: &Complex) -> (f64, f64) {
        ((a.real() - b.real()).abs(), (a.imag() - b.imag()).abs())
    }

    #[test]
    fn complex_basic_operation_test() {
        // Add operation
        let res = Complex::new(1.0, 3.0) + Complex::new(2.0, 4.5);
        let (diff_re, diff_im) = abs_diff(&res, &Complex::new(3.0, 7.5));
        assert!(diff_re < 1e-10 && diff_im < 1e-10);

        let res = Complex::new(1.0, 0.0) + Complex::new(3.4, 0.0);
        let (diff_re, diff_im) = abs_diff(&res, &Complex::new(4.4, 0.0));
        assert!(diff_re < 1e-10 && diff_im < 1e-10);

        // Sub operation
        let res = Complex::new(1.0, 3.0) - Complex::new(2.0, 4.5);
        let (diff_re, diff_im) = abs_diff(&res, &Complex::new(-1.0, -1.5));
        assert!(diff_re < 1e-10 && diff_im < 1e-10);
        
        let res = Complex::new(1.0, 0.0) - Complex::new(3.4, 0.0);
        let (diff_re, diff_im) = abs_diff(&res, &Complex::new(-2.4, 0.0));
        assert!(diff_re < 1e-10 && diff_im < 1e-10);

        // Mul operation
        let res = Complex::new(1.0, 3.0) * Complex::new(2.0, 4.5);
        let (diff_re, diff_im) = abs_diff(&res, &Complex::new(-11.5, 10.5));
        assert!(diff_re < 1e-10 && diff_im < 1e-10);
        
        let res = Complex::new(1.0, 0.0) * Complex::new(3.4, 0.0);
        let (diff_re, diff_im) = abs_diff(&res, &Complex::new(3.4, 0.0));
        assert!(diff_re < 1e-10 && diff_im < 1e-10);

        // Div operation
        let res = Complex::new(1.0, 4.0) / Complex::new(2.0, 2.0);
        let (diff_re, diff_im) = abs_diff(&res, &Complex::new(1.25, 0.75));
        assert!(diff_re < 1e-10 && diff_im < 1e-10);
        
        let res = Complex::new(1.0, 3.5) / Complex::new(4.0, 0.0);
        let (diff_re, diff_im) = abs_diff(&res, &Complex::new(0.25, 0.875));
        assert!(diff_re < 1e-10 && diff_im < 1e-10);

        let res = Complex::new(10.0, 0.0) / Complex::new(4.0, 0.0);
        let (diff_re, diff_im) = abs_diff(&res, &Complex::new(2.5, 0.0));
        assert!(diff_re < 1e-10 && diff_im < 1e-10);
    }

    #[test]
    fn complex_polar_form_transform_test() {
        let c = Complex::new(3.0, 1.5);
        let c = c.to_polar();

        let c = Complex::from_polar(c.norm, c.arg);
        let (diff_re, diff_im) = abs_diff(&c, &Complex::new(3.0, 1.5));
        assert!(diff_re < 1e-10 && diff_im < 1e-10);
    }
}