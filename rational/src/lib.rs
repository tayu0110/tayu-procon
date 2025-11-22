use std::{
    hash::Hash,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, RemAssign, Sub, SubAssign},
};

use zero_one::{One, Zero};

fn reduce_generic<T>(mut num: T, mut den: T) -> (T, T)
where
    T: Clone + Copy + PartialEq + MulAssign + DivAssign + RemAssign + Zero + One,
{
    if den == T::zero() {
        return (T::one(), T::zero());
    }
    if num == T::one() {
        return (T::zero(), T::one());
    }
    let (mut s, mut t) = (num, den);
    while t != T::zero() {
        s %= t;
        (s, t) = (t, s);
    }
    num /= s;
    den /= t;
    (num, den)
}

#[derive(Debug, Clone, Copy)]
pub struct Rational<T> {
    num: T,
    den: T,
}

macro_rules! impl_assign {
    ( $t:ty, $trait:ident, $f:ident, $op:tt ) => {
        impl $trait for Rational<$t> {
            fn $f(&mut self, rhs: Self) {
                *self = *self $op rhs;
            }
        }
    };
}

macro_rules! impl_rational {
    ( $t:ty, $expand:ty ) => {
        impl Rational<$t> {
            fn reduce(num: $t, den: $t) -> ($t, $t) {
                match reduce_generic(num, den) {
                    r @ (1, 0) | r @ (0, 1) => r,
                    (num, den) => (num * den.signum(), den.abs()),
                }
            }

            fn reduce_expanded(num: $expand, den: $expand) -> Result<($t, $t), <$t as TryFrom<$expand>>::Error> {
                #[allow(irrefutable_let_patterns)]
                if let (Ok(num), Ok(den)) = (<$t>::try_from(num), <$t>::try_from(den)) {
                    return Ok(Self::reduce(num, den));
                }
                match reduce_generic(num, den) {
                    (1, 0) => Ok((1, 0)),
                    (0, 1) => Ok((0, 1)),
                    (num, den) => {
                        let (num, den) = (num * den.signum(), den.abs());
                        match (num.try_into(), den.try_into()) {
                            (Ok(num), Ok(den)) => Ok((num, den)),
                            (Err(e), _) | (_, Err(e)) => Err(e),
                        }
                    }
                }
            }

            fn new_reduced(num: $t, den: $t) -> Self {
                Self { num, den }
            }

            pub fn new(num: $t, den: $t) -> Self {
                let (num, den) = Self::reduce(num, den);
                Self { num, den }
            }

            pub fn is_nan(&self) -> bool {
                self.den == 0
            }

            pub fn abs(&self) -> Self {
                Self { num: self.num.abs(), den: self.den }
            }
        }

        impl Add for Rational<$t> {
            type Output = Self;
            fn add(self, rhs: Self) -> Self::Output {
                let den = self.den as $expand * rhs.den as $expand;
                let num = self.den as $expand * rhs.num as $expand + rhs.den as $expand * self.num as $expand;
                let (num, den) = Self::reduce_expanded(num, den).unwrap();
                Self::new_reduced(num, den)
            }
        }

        impl Sub for Rational<$t> {
            type Output = Self;
            fn sub(self, rhs: Self) -> Self::Output {
                self + (-rhs)
            }
        }

        impl Mul for Rational<$t> {
            type Output = Self;
            fn mul(self, rhs: Self) -> Self::Output {
                let num = self.num as $expand * rhs.num as $expand;
                let den = self.den as $expand * rhs.den as $expand;
                let (num, den) = Self::reduce_expanded(num, den).unwrap();
                Self::new_reduced(num, den)
            }
        }

        impl Div for Rational<$t> {
            type Output = Self;
            fn div(self, rhs: Self) -> Self::Output {
                self.mul(Self { num: rhs.den, den: rhs.num })
            }
        }

        impl_assign!($t, AddAssign, add_assign, +);
        impl_assign!($t, SubAssign, sub_assign, -);
        impl_assign!($t, MulAssign, mul_assign, *);
        impl_assign!($t, DivAssign, div_assign, /);

        impl Neg for Rational<$t> {
            type Output = Self;
            fn neg(self) -> Self::Output {
                Self { num: -self.num, den: self.den }
            }
        }

        impl PartialEq for Rational<$t> {
            fn eq(&self, other: &Self) -> bool {
                !self.is_nan() && !other.is_nan() && self.num == other.num && self.den == other.den
            }
        }

        impl PartialOrd for Rational<$t> {
            fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
                (!self.is_nan() && !other.is_nan()).then(|| {
                    let l = self.num as $expand * other.den as $expand;
                    let r = other.num as $expand * self.den as $expand;
                    l.cmp(&r)
                })
            }
        }
    };
}

impl_rational!(i8, i16);
impl_rational!(i16, i32);
impl_rational!(i32, i64);
impl_rational!(i64, i128);
impl_rational!(i128, i128);

impl<T: Hash> Hash for Rational<T> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.num.hash(state);
        self.den.hash(state);
    }
}

impl<T: Zero + One> Zero for Rational<T> {
    fn zero() -> Self {
        Self { num: T::zero(), den: T::one() }
    }
}

impl<T: One> One for Rational<T> {
    fn one() -> Self {
        Self { num: T::one(), den: T::one() }
    }
}
