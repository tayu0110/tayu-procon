pub mod dinic;
pub mod ford_fulkerson;
pub mod hopcroft_karp;

use std::ops::{Add, AddAssign, Sub, SubAssign};

pub use dinic::*;
pub use ford_fulkerson::*;
pub use hopcroft_karp::*;

pub trait Capacity:
    Sized
    + Clone
    + Copy
    + Default
    + PartialEq
    + PartialOrd
    + Add<Output = Self>
    + Sub<Output = Self>
    + AddAssign
    + SubAssign
{
    const MAX: Self;
    const MIN: Self;
}

macro_rules! impl_capacity_to_primitive {
    ( $( $t:ty ),* ) => {
        $(
            impl Capacity for $t {
                const MAX: Self = <$t>::MAX;
                const MIN: Self = <$t>::MIN;
            }
        )*
    };
}

impl_capacity_to_primitive!(
    i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize, f32, f64
);
