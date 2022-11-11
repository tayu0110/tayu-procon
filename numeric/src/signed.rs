use std::ops::Neg;

pub trait Signed : Neg<Output = Self> {
    fn is_negative(self) -> bool;
    fn is_positive(self) -> bool;
    fn signum(self) -> Self;
}

macro_rules! impl_integer_trait {
    ( $t:ty ) => {
        impl Signed for $t {
            fn is_negative(self) -> bool { self.is_negative() }
            fn is_positive(self) -> bool { self.is_positive() }
            fn signum(self) -> Self { self.signum() }
        }
    };
}

impl_integer_trait!(i8);
impl_integer_trait!(i16);
impl_integer_trait!(i32);
impl_integer_trait!(i64);
impl_integer_trait!(i128);
impl_integer_trait!(isize);
