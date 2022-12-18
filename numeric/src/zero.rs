pub trait Zero {
    fn zero() -> Self;
}

macro_rules! impl_zero_integer {
    ( $( $t:ty )* ) => {
        $(impl Zero for $t {
            fn zero() -> $t { 0 }
        })*
    };
}

impl_zero_integer!(i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize);

macro_rules! impl_zero_float {
    ( $( $t:ty )* ) => {
        $(impl Zero for $t {
            fn zero() -> $t { 0.0 }
        })*
    };
}

impl_zero_float!(f32 f64);
