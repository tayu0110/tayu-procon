use std::ops::{
    Rem, RemAssign,
    Shl, Shr, ShlAssign, ShrAssign
};
use super::Numeric;

macro_rules! impl_numeric_trait_for_integer {
    ( $t:tt ) => {
        impl Numeric for $t {
            fn one() -> Self {
                1
            }
            fn zero() -> Self {
                0
            }
            fn max_value() -> Self {
                std::$t::MAX
            }
            fn min_value() -> Self {
                std::$t::MIN
            }
        }
    };
}

impl_numeric_trait_for_integer!(u8);
impl_numeric_trait_for_integer!(u16);
impl_numeric_trait_for_integer!(u32);
impl_numeric_trait_for_integer!(u64);
impl_numeric_trait_for_integer!(u128);
impl_numeric_trait_for_integer!(usize);
impl_numeric_trait_for_integer!(i8);
impl_numeric_trait_for_integer!(i16);
impl_numeric_trait_for_integer!(i32);
impl_numeric_trait_for_integer!(i64);
impl_numeric_trait_for_integer!(i128);
impl_numeric_trait_for_integer!(isize);

pub trait Integer
        : Numeric + Rem<Self, Output = Self> + RemAssign
          + Shl<Self, Output = Self> + Shr<Self, Output = Self> + ShlAssign + ShrAssign
          + std::hash::Hash + Eq + Ord {
    fn abs_diff(self, other: Self) -> Self;
    fn count_ones(self) -> u32;
    fn count_zeros(self) -> u32;
    fn div_euclid(self, rhs: Self) -> Self;
    fn leading_ones(self) -> u32;
    fn leading_zeros(self) -> u32;
    fn pow(self, exp: u32) -> Self;
    fn rem_euclid(self, rhs: Self) -> Self;
    fn reverse_bits(self) -> Self;
    fn rotate_left(self, n: u32) -> Self;
    fn rotate_right(self, n: u32) -> Self;
    fn swap_bytes(self) -> Self;
    fn trailing_ones(self) -> u32;
    fn trailing_zeros(self) -> u32;
}

macro_rules! impl_integer_trait {
    ( $t:ty ) => {
        impl Integer for $t {
            fn abs_diff(self, other: Self) -> Self { std::cmp::max(self, other) - std::cmp::min(self, other) }
            fn count_ones(self) -> u32 { self.count_ones() }
            fn count_zeros(self) -> u32 { self.count_zeros() }
            fn div_euclid(self, rhs: Self) -> Self { self.div_euclid(rhs) }
            fn leading_ones(self) -> u32 { (!self).leading_zeros() }
            fn leading_zeros(self) -> u32 { self.leading_zeros() }
            fn pow(self, exp: u32) -> Self { self.pow(exp) }
            fn rem_euclid(self, rhs: Self) -> Self { self.rem_euclid(rhs) }
            fn reverse_bits(self) -> Self { self.reverse_bits() }
            fn rotate_left(self, n: u32) -> Self { self.rotate_left(n) }
            fn rotate_right(self, n: u32) -> Self { self.rotate_right(n) }
            fn swap_bytes(self) -> Self { self.swap_bytes() }
            fn trailing_ones(self) -> u32 { (!self).trailing_zeros() }
            fn trailing_zeros(self) -> u32 { self.trailing_zeros() }
        }
    };
}

impl_integer_trait!(u8);
impl_integer_trait!(u16);
impl_integer_trait!(u32);
impl_integer_trait!(u64);
impl_integer_trait!(u128);
impl_integer_trait!(usize);
impl_integer_trait!(i8);
impl_integer_trait!(i16);
impl_integer_trait!(i32);
impl_integer_trait!(i64);
impl_integer_trait!(i128);
impl_integer_trait!(isize);


