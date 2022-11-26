use super::Numeric;
use std::num::FpCategory;
use std::ops::Neg;

macro_rules! impl_numeric_trait_for_float {
    ( $t:tt ) => {
        impl Numeric for $t {
            fn max_value() -> Self {
                std::$t::MAX
            }
            fn min_value() -> Self {
                std::$t::MIN
            }
        }
    };
}

impl_numeric_trait_for_float!(f32);
impl_numeric_trait_for_float!(f64);

pub trait Float: Numeric + Neg<Output = Self> {
    fn abs(self) -> Self;
    fn acos(self) -> Self;
    fn acosh(self) -> Self;
    fn asin(self) -> Self;
    fn asinh(self) -> Self;
    fn atan(self) -> Self;
    fn atan2(self, other: Self) -> Self;
    fn atanh(self) -> Self;
    fn cbrt(self) -> Self;
    fn ceil(self) -> Self;
    fn classify(self) -> FpCategory;
    fn copysign(self, sign: Self) -> Self;
    fn cos(self) -> Self;
    fn cosh(self) -> Self;
    fn div_euclid(self, rhs: Self) -> Self;
    fn exp(self) -> Self;
    fn exp2(self) -> Self;
    fn exp_m1(self) -> Self;
    fn floor(self) -> Self;
    fn fract(self) -> Self;
    fn hypot(self, other: Self) -> Self;
    fn is_finite(self) -> bool;
    fn is_infinite(self) -> bool;
    fn is_nan(self) -> bool;
    fn is_normal(self) -> bool;
    fn is_sign_negative(self) -> bool;
    fn is_sign_positive(self) -> bool;
    fn ln(self) -> Self;
    fn ln_1p(self) -> Self;
    fn log(self, base: Self) -> Self;
    fn log10(self) -> Self;
    fn log2(self) -> Self;
    fn max(self, other: Self) -> Self;
    fn min(self, other: Self) -> Self;
    fn mul_add(self, a: Self, b: Self) -> Self;
    fn powf(self, n: Self) -> Self;
    fn powi(self, n: i32) -> Self;
    fn recip(self) -> Self;
    fn rem_euclid(self, rhs: Self) -> Self;
    fn round(self) -> Self;
    fn signum(self) -> Self;
    fn sin(self) -> Self;
    fn sin_cos(self) -> (Self, Self);
    fn sinh(self) -> Self;
    fn sqrt(self) -> Self;
    fn tan(self) -> Self;
    fn tanh(self) -> Self;
    fn to_radians(self) -> Self;
    fn trunc(self) -> Self;
    fn pi() -> Self;
}

macro_rules! impl_float_trait {
    ( $t:tt ) => {
        impl Float for $t {
            fn abs(self) -> Self {
                self.abs()
            }
            fn acos(self) -> Self {
                self.acos()
            }
            fn acosh(self) -> Self {
                self.acosh()
            }
            fn asin(self) -> Self {
                self.asin()
            }
            fn asinh(self) -> Self {
                self.asinh()
            }
            fn atan(self) -> Self {
                self.atan()
            }
            fn atan2(self, other: Self) -> Self {
                self.atan2(other)
            }
            fn atanh(self) -> Self {
                self.atanh()
            }
            fn cbrt(self) -> Self {
                self.cbrt()
            }
            fn ceil(self) -> Self {
                self.ceil()
            }
            fn classify(self) -> FpCategory {
                self.classify()
            }
            fn copysign(self, sign: Self) -> Self {
                self.copysign(sign)
            }
            fn cos(self) -> Self {
                self.cos()
            }
            fn cosh(self) -> Self {
                self.cosh()
            }
            fn div_euclid(self, rhs: Self) -> Self {
                self.div_euclid(rhs)
            }
            fn exp(self) -> Self {
                self.exp()
            }
            fn exp2(self) -> Self {
                self.exp2()
            }
            fn exp_m1(self) -> Self {
                self.exp_m1()
            }
            fn floor(self) -> Self {
                self.floor()
            }
            fn fract(self) -> Self {
                self.fract()
            }
            fn hypot(self, other: Self) -> Self {
                self.hypot(other)
            }
            fn is_finite(self) -> bool {
                self.is_finite()
            }
            fn is_infinite(self) -> bool {
                self.is_infinite()
            }
            fn is_nan(self) -> bool {
                self.is_nan()
            }
            fn is_normal(self) -> bool {
                self.is_normal()
            }
            fn is_sign_negative(self) -> bool {
                self.is_sign_negative()
            }
            fn is_sign_positive(self) -> bool {
                self.is_sign_positive()
            }
            fn ln(self) -> Self {
                self.ln()
            }
            fn ln_1p(self) -> Self {
                self.ln_1p()
            }
            fn log(self, base: Self) -> Self {
                self.log(base)
            }
            fn log10(self) -> Self {
                self.log10()
            }
            fn log2(self) -> Self {
                self.log2()
            }
            fn max(self, other: Self) -> Self {
                self.max(other)
            }
            fn min(self, other: Self) -> Self {
                self.min(other)
            }
            fn mul_add(self, a: Self, b: Self) -> Self {
                self.mul_add(a, b)
            }
            fn powf(self, n: Self) -> Self {
                self.powf(n)
            }
            fn powi(self, n: i32) -> Self {
                self.powi(n)
            }
            fn recip(self) -> Self {
                self.recip()
            }
            fn rem_euclid(self, rhs: Self) -> Self {
                self.rem_euclid(rhs)
            }
            fn round(self) -> Self {
                self.round()
            }
            fn signum(self) -> Self {
                self.signum()
            }
            fn sin(self) -> Self {
                self.sin()
            }
            fn sin_cos(self) -> (Self, Self) {
                self.sin_cos()
            }
            fn sinh(self) -> Self {
                self.sinh()
            }
            fn sqrt(self) -> Self {
                self.sqrt()
            }
            fn tan(self) -> Self {
                self.tan()
            }
            fn tanh(self) -> Self {
                self.tanh()
            }
            fn to_radians(self) -> Self {
                self.to_radians()
            }
            fn trunc(self) -> Self {
                self.trunc()
            }
            fn pi() -> Self {
                std::$t::consts::PI
            }
        }
    };
}

impl_float_trait!(f64);
impl_float_trait!(f32);
