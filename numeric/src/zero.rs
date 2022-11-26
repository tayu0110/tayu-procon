pub trait Zero {
    fn zero() -> Self;
}

macro_rules! impl_zero_integer {
    ( $t:ty ) => {
        impl Zero for $t {
            fn zero() -> $t {
                0
            }
        }
    };
}

impl_zero_integer!(i8);
impl_zero_integer!(i16);
impl_zero_integer!(i32);
impl_zero_integer!(i64);
impl_zero_integer!(i128);
impl_zero_integer!(isize);
impl_zero_integer!(u8);
impl_zero_integer!(u16);
impl_zero_integer!(u32);
impl_zero_integer!(u64);
impl_zero_integer!(u128);
impl_zero_integer!(usize);

macro_rules! impl_zero_float {
    ( $t:ty ) => {
        impl Zero for $t {
            fn zero() -> $t {
                0.0
            }
        }
    };
}

impl_zero_float!(f32);
impl_zero_float!(f64);
