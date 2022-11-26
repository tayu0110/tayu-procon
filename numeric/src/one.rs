pub trait One {
    fn one() -> Self;
}

macro_rules! impl_one_integer {
    ( $t:ty ) => {
        impl One for $t {
            fn one() -> $t {
                1
            }
        }
    };
}

impl_one_integer!(i8);
impl_one_integer!(i16);
impl_one_integer!(i32);
impl_one_integer!(i64);
impl_one_integer!(i128);
impl_one_integer!(isize);
impl_one_integer!(u8);
impl_one_integer!(u16);
impl_one_integer!(u32);
impl_one_integer!(u64);
impl_one_integer!(u128);
impl_one_integer!(usize);

macro_rules! impl_one_float {
    ( $t:ty ) => {
        impl One for $t {
            fn one() -> $t {
                1.0
            }
        }
    };
}

impl_one_float!(f32);
impl_one_float!(f64);
