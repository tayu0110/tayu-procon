pub trait One {
    fn one() -> Self;
}

macro_rules! impl_one_integer {
    ( $( $t:ty )* ) => {
        $(impl One for $t {
            fn one() -> $t { 1 }
        })*
    };
}

impl_one_integer!(i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize);

macro_rules! impl_one_float {
    ( $( $t:ty )* ) => {
        $(impl One for $t {
            fn one() -> $t { 1.0 }
        })*
    };
}

impl_one_float!(f32 f64);
