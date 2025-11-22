use super::Numeric;
use std::ops::Neg;

macro_rules! impl_numeric_trait_for_float {
    ( $( $t:tt )* ) => {
        $(impl Numeric for $t {
            fn max_value() -> Self { $t::MAX }
            fn min_value() -> Self { $t::MIN }
        })*
    };
}

impl_numeric_trait_for_float!(f32 f64);

pub trait Float: Numeric + Neg<Output = Self> {
    fn abs(self) -> Self;
    fn acos(self) -> Self;
    fn asin(self) -> Self;
    fn atan(self) -> Self;
    fn atan2(self, other: Self) -> Self;
    fn cbrt(self) -> Self;
    fn ceil(self) -> Self;
    fn cos(self) -> Self;
    fn floor(self) -> Self;
    fn hypot(self, other: Self) -> Self;
    fn is_infinite(self) -> bool;
    fn is_nan(self) -> bool;
    fn max(self, other: Self) -> Self;
    fn min(self, other: Self) -> Self;
    fn mul_add(self, a: Self, b: Self) -> Self;
    fn powf(self, n: Self) -> Self;
    fn powi(self, n: i32) -> Self;
    fn round(self) -> Self;
    fn signum(self) -> Self;
    fn sin(self) -> Self;
    fn sqrt(self) -> Self;
    fn tan(self) -> Self;
    fn to_radians(self) -> Self;
    fn pi() -> Self;
}

macro_rules! impl_float_trait {
    ( $( $t:tt )* ) => {
        $(impl Float for $t {
            fn abs(self) -> Self { self.abs() }
            fn acos(self) -> Self { self.acos() }
            fn asin(self) -> Self { self.asin() }
            fn atan(self) -> Self { self.atan() }
            fn atan2(self, other: Self) -> Self { self.atan2(other) }
            fn cbrt(self) -> Self { self.cbrt() }
            fn ceil(self) -> Self { self.ceil() }
            fn cos(self) -> Self { self.cos() }
            fn floor(self) -> Self { self.floor() }
            fn hypot(self, other: Self) -> Self { self.hypot(other) }
            fn is_infinite(self) -> bool { self.is_infinite() }
            fn is_nan(self) -> bool { self.is_nan() }
            fn max(self, other: Self) -> Self { self.max(other) }
            fn min(self, other: Self) -> Self { self.min(other) }
            fn mul_add(self, a: Self, b: Self) -> Self { self.mul_add(a, b) }
            fn powf(self, n: Self) -> Self { self.powf(n) }
            fn powi(self, n: i32) -> Self { self.powi(n) }
            fn round(self) -> Self { self.round() }
            fn signum(self) -> Self { self.signum() }
            fn sin(self) -> Self { self.sin() }
            fn sqrt(self) -> Self { self.sqrt() }
            fn tan(self) -> Self { self.tan() }
            fn to_radians(self) -> Self { self.to_radians() }
            fn pi() -> Self { std::$t::consts::PI }
        })*
    };
}

impl_float_trait!(f32 f64);
