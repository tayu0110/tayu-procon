use std::ops::Neg;

pub trait Signed: Neg<Output = Self> + std::marker::Sized {
    fn is_negative(self) -> bool;
    fn is_positive(self) -> bool;
}

macro_rules! impl_integer_trait {
    ( $( $t:ty )* ) => {
        $(impl Signed for $t {
            fn is_negative(self) -> bool {
                self.is_negative()
            }
            fn is_positive(self) -> bool {
                self.is_positive()
            }
        })*
    };
}

impl_integer_trait!(i8 i16 i32 i64 i128 isize);
