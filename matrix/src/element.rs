use modint::{Modint, Modulo, MontgomeryModint};
use numeric::{One, Zero};
use std::ops::{Add, Div, Mul, Sub};

pub trait MatrixElement: Clone + Copy + Add<Self, Output = Self> + Sub<Self, Output = Self> + Mul<Self, Output = Self> + Div<Self, Output = Self> + PartialEq + One + Zero + Sized {
    fn is_zero(self) -> bool;
    fn abs(self) -> Self;
}

macro_rules! impl_matrix_element_for_integer {
    ( $( $t:ty ,)* ) => {
        $(impl MatrixElement for $t {
            fn is_zero(self) -> bool { self == 0 }
            #[allow(unused_comparisons)]
            fn abs(self) -> Self { if self < 0 { 0 - self } else { self } }
        })*
    };
}

impl_matrix_element_for_integer!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize,);

impl<M: Modulo> MatrixElement for Modint<M> {
    fn is_zero(self) -> bool { self == Modint::<M>::zero() }
    fn abs(self) -> Self { self }
}
impl<M: Modulo> MatrixElement for MontgomeryModint<M> {
    fn is_zero(self) -> bool { self == MontgomeryModint::<M>::zero() }
    fn abs(self) -> Self { self }
}

impl MatrixElement for f32 {
    fn is_zero(self) -> bool { self.abs() < 1e-8 }
    fn abs(self) -> Self { self.abs() }
}
impl MatrixElement for f64 {
    fn is_zero(self) -> bool { self.abs() < 1e-8 }
    fn abs(self) -> Self { self.abs() }
}
