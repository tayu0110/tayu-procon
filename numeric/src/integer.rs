use super::Numeric;
use std::ops::{
    BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Rem, RemAssign, Shl, ShlAssign,
    Shr, ShrAssign,
};

macro_rules! impl_numeric_trait_for_integer {
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

pub trait Integer:
    Numeric
    + Rem<Self, Output = Self>
    + RemAssign
    + Shl<i8, Output = Self>
    + Shl<i16, Output = Self>
    + Shl<i32, Output = Self>
    + Shl<i64, Output = Self>
    + Shl<i128, Output = Self>
    + Shl<isize, Output = Self>
    + Shl<u8, Output = Self>
    + Shl<u16, Output = Self>
    + Shl<u32, Output = Self>
    + Shl<u64, Output = Self>
    + Shl<u128, Output = Self>
    + Shl<usize, Output = Self>
    + Shr<i8, Output = Self>
    + Shr<i16, Output = Self>
    + Shr<i32, Output = Self>
    + Shr<i64, Output = Self>
    + Shr<i128, Output = Self>
    + Shr<isize, Output = Self>
    + Shr<u8, Output = Self>
    + Shr<u16, Output = Self>
    + Shr<u32, Output = Self>
    + Shr<u64, Output = Self>
    + Shr<u128, Output = Self>
    + Shr<usize, Output = Self>
    + Shl<i8, Output = Self>
    + Shl<i16, Output = Self>
    + Shl<i32, Output = Self>
    + Shl<i64, Output = Self>
    + Shl<i128, Output = Self>
    + Shl<isize, Output = Self>
    + Shl<u8, Output = Self>
    + Shl<u16, Output = Self>
    + Shl<u32, Output = Self>
    + Shl<u64, Output = Self>
    + Shl<u128, Output = Self>
    + Shl<usize, Output = Self>
    + ShlAssign<i8>
    + ShlAssign<i16>
    + ShlAssign<i32>
    + ShlAssign<i64>
    + ShlAssign<i128>
    + ShlAssign<isize>
    + ShlAssign<u8>
    + ShlAssign<u16>
    + ShlAssign<u32>
    + ShlAssign<u64>
    + ShlAssign<u128>
    + ShlAssign<usize>
    + ShrAssign<i8>
    + ShrAssign<i16>
    + ShrAssign<i32>
    + ShrAssign<i64>
    + ShrAssign<i128>
    + ShrAssign<isize>
    + ShrAssign<u8>
    + ShrAssign<u16>
    + ShrAssign<u32>
    + ShrAssign<u64>
    + ShrAssign<u128>
    + ShrAssign<usize>
    + BitAnd<Self, Output = Self>
    + BitOr<Self, Output = Self>
    + BitXor<Self, Output = Self>
    + BitAndAssign
    + BitOrAssign
    + BitXorAssign
    + std::hash::Hash
    + Eq
    + Ord
{
    fn abs_diff(self, other: Self) -> Self;
    fn count_ones(self) -> u32;
    fn count_zeros(self) -> u32;
    fn div_euclid(self, rhs: Self) -> Self;
    fn leading_ones(self) -> u32;
    fn leading_zeros(self) -> u32;
    fn rem_euclid(self, rhs: Self) -> Self;
    fn reverse_bits(self) -> Self;
    fn rotate_left(self, n: u32) -> Self;
    fn rotate_right(self, n: u32) -> Self;
    fn trailing_ones(self) -> u32;
    fn trailing_zeros(self) -> u32;
    fn overflowing_add(self, rhs: Self) -> (Self, bool);
    fn overflowing_div(self, rhs: Self) -> (Self, bool);
    fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool);
    fn overflowing_mul(self, rhs: Self) -> (Self, bool);
    fn overflowing_neg(self) -> (Self, bool);
    fn overflowing_pow(self, rhs: u32) -> (Self, bool);
    fn overflowing_rem(self, rhs: Self) -> (Self, bool);
    fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool);
    fn overflowing_shl(self, rhs: u32) -> (Self, bool);
    fn overflowing_shr(self, rhs: u32) -> (Self, bool);
    fn overflowing_sub(self, rhs: Self) -> (Self, bool);
    fn saturating_add(self, rhs: Self) -> Self;
    fn saturating_mul(self, rhs: Self) -> Self;
    fn saturating_pow(self, rhs: u32) -> Self;
    fn saturating_sub(self, rhs: Self) -> Self;
    fn wrapping_add(self, rhs: Self) -> Self;
    fn wrapping_div(self, rhs: Self) -> Self;
    fn wrapping_div_euclid(self, rhs: Self) -> Self;
    fn wrapping_mul(self, rhs: Self) -> Self;
    fn wrapping_neg(self) -> Self;
    fn wrapping_pow(self, rhs: u32) -> Self;
    fn wrapping_rem(self, rhs: Self) -> Self;
    fn wrapping_rem_euclid(self, rhs: Self) -> Self;
    fn wrapping_shl(self, rhs: u32) -> Self;
    fn wrapping_shr(self, rhs: u32) -> Self;
    fn wrapping_sub(self, rhs: Self) -> Self;
}

macro_rules! impl_integer_trait {
    ( $t:ty ) => {
        impl Integer for $t {
            fn abs_diff(self, other: Self) -> Self {
                std::cmp::max(self, other) - std::cmp::min(self, other)
            }
            fn count_ones(self) -> u32 {
                self.count_ones()
            }
            fn count_zeros(self) -> u32 {
                self.count_zeros()
            }
            fn div_euclid(self, rhs: Self) -> Self {
                self.div_euclid(rhs)
            }
            fn leading_ones(self) -> u32 {
                (!self).leading_zeros()
            }
            fn leading_zeros(self) -> u32 {
                self.leading_zeros()
            }
            fn rem_euclid(self, rhs: Self) -> Self {
                self.rem_euclid(rhs)
            }
            fn reverse_bits(self) -> Self {
                self.reverse_bits()
            }
            fn rotate_left(self, n: u32) -> Self {
                self.rotate_left(n)
            }
            fn rotate_right(self, n: u32) -> Self {
                self.rotate_right(n)
            }
            fn trailing_ones(self) -> u32 {
                (!self).trailing_zeros()
            }
            fn trailing_zeros(self) -> u32 {
                self.trailing_zeros()
            }
            fn overflowing_add(self, rhs: Self) -> (Self, bool) {
                self.overflowing_add(rhs)
            }
            fn overflowing_div(self, rhs: Self) -> (Self, bool) {
                self.overflowing_div(rhs)
            }
            fn overflowing_div_euclid(self, rhs: Self) -> (Self, bool) {
                self.overflowing_div_euclid(rhs)
            }
            fn overflowing_mul(self, rhs: Self) -> (Self, bool) {
                self.overflowing_mul(rhs)
            }
            fn overflowing_neg(self) -> (Self, bool) {
                self.overflowing_neg()
            }
            fn overflowing_pow(self, rhs: u32) -> (Self, bool) {
                self.overflowing_pow(rhs)
            }
            fn overflowing_rem(self, rhs: Self) -> (Self, bool) {
                self.overflowing_rem(rhs)
            }
            fn overflowing_rem_euclid(self, rhs: Self) -> (Self, bool) {
                self.overflowing_rem_euclid(rhs)
            }
            fn overflowing_shl(self, rhs: u32) -> (Self, bool) {
                self.overflowing_shl(rhs)
            }
            fn overflowing_shr(self, rhs: u32) -> (Self, bool) {
                self.overflowing_shr(rhs)
            }
            fn overflowing_sub(self, rhs: Self) -> (Self, bool) {
                self.overflowing_sub(rhs)
            }
            fn saturating_add(self, rhs: Self) -> Self {
                self.saturating_add(rhs)
            }
            fn saturating_mul(self, rhs: Self) -> Self {
                self.saturating_mul(rhs)
            }
            fn saturating_pow(self, rhs: u32) -> Self {
                self.saturating_pow(rhs)
            }
            fn saturating_sub(self, rhs: Self) -> Self {
                self.saturating_sub(rhs)
            }
            fn wrapping_add(self, rhs: Self) -> Self {
                self.wrapping_add(rhs)
            }
            fn wrapping_div(self, rhs: Self) -> Self {
                self.wrapping_div(rhs)
            }
            fn wrapping_div_euclid(self, rhs: Self) -> Self {
                self.wrapping_div_euclid(rhs)
            }
            fn wrapping_mul(self, rhs: Self) -> Self {
                self.wrapping_mul(rhs)
            }
            fn wrapping_neg(self) -> Self {
                self.wrapping_neg()
            }
            fn wrapping_pow(self, rhs: u32) -> Self {
                self.wrapping_pow(rhs)
            }
            fn wrapping_rem(self, rhs: Self) -> Self {
                self.wrapping_rem(rhs)
            }
            fn wrapping_rem_euclid(self, rhs: Self) -> Self {
                self.wrapping_rem_euclid(rhs)
            }
            fn wrapping_shl(self, rhs: u32) -> Self {
                self.wrapping_shl(rhs)
            }
            fn wrapping_shr(self, rhs: u32) -> Self {
                self.wrapping_shr(rhs)
            }
            fn wrapping_sub(self, rhs: Self) -> Self {
                self.wrapping_sub(rhs)
            }
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
