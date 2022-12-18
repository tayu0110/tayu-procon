use super::Numeric;
use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Rem, RemAssign, Shl, ShlAssign, Shr, ShrAssign};

macro_rules! impl_numeric_trait_for_integer {
    ( $( $t:tt )* ) => {
        $(impl Numeric for $t {
            fn max_value() -> Self { std::$t::MAX }
            fn min_value() -> Self { std::$t::MIN }
        })*
    };
}

impl_numeric_trait_for_integer!(i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize);

pub trait Integer:
    Numeric
    + Rem<Self, Output = Self>
    + RemAssign
    + Shl<i32, Output = Self>
    + Shl<i64, Output = Self>
    + Shl<u32, Output = Self>
    + Shl<u64, Output = Self>
    + Shl<usize, Output = Self>
    + Shr<i32, Output = Self>
    + Shr<i64, Output = Self>
    + Shr<u32, Output = Self>
    + Shr<u64, Output = Self>
    + Shr<usize, Output = Self>
    + ShlAssign<i32>
    + ShlAssign<i64>
    + ShlAssign<u32>
    + ShlAssign<u64>
    + ShlAssign<usize>
    + ShrAssign<i32>
    + ShrAssign<i64>
    + ShrAssign<u32>
    + ShrAssign<u64>
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
    fn overflowing_mul(self, rhs: Self) -> (Self, bool);
    fn overflowing_neg(self) -> (Self, bool);
    fn overflowing_shl(self, rhs: u32) -> (Self, bool);
    fn overflowing_shr(self, rhs: u32) -> (Self, bool);
    fn overflowing_sub(self, rhs: Self) -> (Self, bool);
    fn saturating_add(self, rhs: Self) -> Self;
    fn saturating_mul(self, rhs: Self) -> Self;
    fn saturating_sub(self, rhs: Self) -> Self;
    fn wrapping_add(self, rhs: Self) -> Self;
    fn wrapping_mul(self, rhs: Self) -> Self;
    fn wrapping_neg(self) -> Self;
    fn wrapping_shl(self, rhs: u32) -> Self;
    fn wrapping_shr(self, rhs: u32) -> Self;
    fn wrapping_sub(self, rhs: Self) -> Self;
}

macro_rules! impl_integer_trait {
    ( $( $t:ty )* ) => {
        $(impl Integer for $t {
            fn abs_diff(self, other: Self) -> Self { std::cmp::max(self, other) - std::cmp::min(self, other) }
            fn count_ones(self) -> u32 { self.count_ones() }
            fn count_zeros(self) -> u32 { self.count_zeros() }
            fn div_euclid(self, rhs: Self) -> Self { self.div_euclid(rhs) }
            fn leading_ones(self) -> u32 { (!self).leading_zeros() }
            fn leading_zeros(self) -> u32 { self.leading_zeros() }
            fn rem_euclid(self, rhs: Self) -> Self { self.rem_euclid(rhs) }
            fn reverse_bits(self) -> Self { self.reverse_bits() }
            fn rotate_left(self, n: u32) -> Self { self.rotate_left(n) }
            fn rotate_right(self, n: u32) -> Self { self.rotate_right(n) }
            fn trailing_ones(self) -> u32 { (!self).trailing_zeros() }
            fn trailing_zeros(self) -> u32 { self.trailing_zeros() }
            fn overflowing_add(self, rhs: Self) -> (Self, bool) { self.overflowing_add(rhs) }
            fn overflowing_mul(self, rhs: Self) -> (Self, bool) { self.overflowing_mul(rhs) }
            fn overflowing_neg(self) -> (Self, bool) { self.overflowing_neg() }
            fn overflowing_shl(self, rhs: u32) -> (Self, bool) { self.overflowing_shl(rhs) }
            fn overflowing_shr(self, rhs: u32) -> (Self, bool) { self.overflowing_shr(rhs) }
            fn overflowing_sub(self, rhs: Self) -> (Self, bool) { self.overflowing_sub(rhs) }
            fn saturating_add(self, rhs: Self) -> Self { self.saturating_add(rhs) }
            fn saturating_mul(self, rhs: Self) -> Self { self.saturating_mul(rhs) }
            fn saturating_sub(self, rhs: Self) -> Self { self.saturating_sub(rhs) }
            fn wrapping_add(self, rhs: Self) -> Self { self.wrapping_add(rhs) }
            fn wrapping_mul(self, rhs: Self) -> Self { self.wrapping_mul(rhs) }
            fn wrapping_neg(self) -> Self { self.wrapping_neg() }
            fn wrapping_shl(self, rhs: u32) -> Self { self.wrapping_shl(rhs) }
            fn wrapping_shr(self, rhs: u32) -> Self { self.wrapping_shr(rhs) }
            fn wrapping_sub(self, rhs: Self) -> Self { self.wrapping_sub(rhs) }
        })*
    };
}

impl_integer_trait!(i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize);
