/////////////////////////////////////////////////////////////////////////////
///
/// Complex Number
///
/////////////////////////////////////////////////////////////////////////////
use numeric::float::Float;
use numeric::{One, Zero};
use std::convert::From;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

#[derive(Clone, Copy, PartialEq, PartialOrd)]
pub struct Complex<T: Float = f64> {
    re: T,
    im: T,
}

impl<T: Float> One for Complex<T> {
    #[inline]
    fn one() -> Self { Self::one() }
}

impl<T: Float> Zero for Complex<T> {
    #[inline]
    fn zero() -> Self { Self::zero() }
}

impl<T: Float> Complex<T> {
    #[inline]
    pub fn new(re: T, im: T) -> Self { Self { re, im } }

    #[inline]
    pub fn zero() -> Self { Self { re: T::zero(), im: T::zero() } }

    #[inline]
    pub fn one() -> Self { Self { re: T::one(), im: T::zero() } }

    #[inline]
    pub fn real(&self) -> T { self.re }

    #[inline]
    pub fn imag(&self) -> T { self.im }

    #[inline]
    pub fn norm_sq(&self) -> T { self.re * self.re + self.im * self.im }

    #[inline]
    pub fn norm(&self) -> T { self.norm_sq().sqrt() }

    #[inline]
    pub fn arg(&self) -> T { self.im.atan2(self.re) }

    #[inline]
    pub fn from_polar(norm: T, arg: T) -> Self {
        Self {
            re: norm * arg.cos(),
            im: norm * arg.sin(),
        }
    }

    #[inline]
    pub fn conjugate(&self) -> Self { Self { re: self.re, im: -self.im } }
}

impl<T: Float> Add for Complex<T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output { Self::new(self.re + rhs.re, self.im + rhs.im) }
}

impl<T: Float> Sub for Complex<T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output { Self::new(self.re - rhs.re, self.im - rhs.im) }
}

impl<T: Float> Mul for Complex<T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output { Self::new(self.re * rhs.re - self.im * rhs.im, self.re * rhs.im + self.im * rhs.re) }
}

impl<T: Float> Div for Complex<T> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        let c = self * Self::new(rhs.re, -rhs.im);
        let norm2 = rhs.re * rhs.re + rhs.im * rhs.im;
        Self::new(c.re / norm2, c.im / norm2)
    }
}

impl<T: Float> AddAssign for Complex<T> {
    fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<T: Float> SubAssign for Complex<T> {
    fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<T: Float> MulAssign for Complex<T> {
    fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<T: Float> DivAssign for Complex<T> {
    fn div_assign(&mut self, rhs: Self) { *self = *self / rhs; }
}

impl<T: Float> From<T> for Complex<T> {
    fn from(from: T) -> Self { Self::new(from, T::zero()) }
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

impl std::fmt::Debug for Complex<f32> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut s = format!("{}", self.real());
        if self.imag().abs() > 1e-20 {
            s += format!("{:+}i", self.imag()).as_str();
        }
        write!(f, "{}", s)
    }
}

macro_rules! impl_basic_operation_with_float_number {
    ( $t:ty ) => {
        impl Add<$t> for Complex<$t> {
            type Output = Complex<$t>;
            fn add(self, rhs: $t) -> Self::Output { Self::new(self.real() + rhs, self.imag()) }
        }

        impl Sub<$t> for Complex<$t> {
            type Output = Complex<$t>;
            fn sub(self, rhs: $t) -> Self::Output { Self::new(self.real() - rhs, self.imag()) }
        }

        impl Mul<$t> for Complex<$t> {
            type Output = Complex<$t>;
            fn mul(self, rhs: $t) -> Self::Output { Self::new(self.real() * rhs, self.imag() * rhs) }
        }

        impl Div<$t> for Complex<$t> {
            type Output = Complex<$t>;
            fn div(self, rhs: $t) -> Self::Output { Self::new(self.real() / rhs, self.imag() / rhs) }
        }

        impl AddAssign<$t> for Complex<$t> {
            fn add_assign(&mut self, rhs: $t) { self.re += rhs; }
        }

        impl SubAssign<$t> for Complex<$t> {
            fn sub_assign(&mut self, rhs: $t) { self.re -= rhs; }
        }

        impl MulAssign<$t> for Complex<$t> {
            fn mul_assign(&mut self, rhs: $t) {
                self.re *= rhs;
                self.im *= rhs;
            }
        }

        impl DivAssign<$t> for Complex<$t> {
            fn div_assign(&mut self, rhs: $t) {
                self.re /= rhs;
                self.im /= rhs;
            }
        }
    };
}

impl_basic_operation_with_float_number!(f64);
impl_basic_operation_with_float_number!(f32);

#[cfg(test)]
mod tests {
    use super::Complex;

    fn abs_diff(a: &Complex, b: &Complex) -> (f64, f64) { ((a.real() - b.real()).abs(), (a.imag() - b.imag()).abs()) }

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
}
