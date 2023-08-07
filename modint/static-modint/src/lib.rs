pub use modint_common::*;

use numeric::{One, Zero};
use std::marker::{self, PhantomData};
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct StaticModint<M: Modulo> {
    val: u32,
    _p: PhantomData<fn() -> M>,
}

impl<M: Modulo> One for StaticModint<M> {
    #[inline]
    fn one() -> Self { Self::one() }
}

impl<M: Modulo> Zero for StaticModint<M> {
    #[inline]
    fn zero() -> Self { Self::zero() }
}

impl<M: Modulo> StaticModint<M> {
    #[inline]
    pub const fn new(val: u64) -> Self { StaticModint { val: (val % M::N as u64) as u32, _p: PhantomData } }

    pub const fn new_signed(val: i64) -> Self { StaticModint { val: val.rem_euclid(M::N as i64) as u32, _p: PhantomData } }

    #[inline]
    pub const fn raw(val: u32) -> Self {
        debug_assert!(val < M::N);
        StaticModint { val, _p: marker::PhantomData }
    }

    #[inline]
    pub const fn zero() -> Self { StaticModint { val: 0, _p: marker::PhantomData } }

    #[inline]
    pub const fn one() -> Self { StaticModint { val: 1, _p: marker::PhantomData } }

    #[inline]
    pub const fn modulo() -> u32 { M::N }

    #[inline]
    pub const fn val(&self) -> u32 { self.val }

    pub const fn pow(&self, mut exp: u32) -> Self {
        let (mut val, mut res) = (self.val as u64, 1);
        while exp > 0 {
            if exp & 1 == 1 {
                res = (res * val) % M::N as u64;
            }
            val = (val * val) % M::N as u64;
            exp >>= 1;
        }
        Self { val: res as u32, _p: PhantomData }
    }

    #[inline]
    pub const fn inv(&self) -> Self { self.pow(M::N - 2) }

    #[inline]
    pub const fn nth_root(n: u32) -> Self {
        debug_assert!(n == 1 << n.trailing_zeros());
        StaticModint::raw(M::PRIM_ROOT).pow((M::N - 1) / n)
    }

    #[inline]
    pub const fn add_raw(&self, rhs: u32) -> Self {
        debug_assert!(rhs < M::N);
        let res = self.val + rhs;
        StaticModint::raw(if res >= M::N { res - M::N } else { res })
    }

    #[inline]
    pub const fn sub_raw(&self, rhs: u32) -> Self {
        debug_assert!(rhs < M::N);
        let (res, f) = self.val.overflowing_sub(rhs);
        StaticModint::raw(if f { res.wrapping_add(M::N) } else { res })
    }

    #[inline]
    pub const fn mul_raw(&self, rhs: u32) -> Self {
        debug_assert!(rhs < M::N);
        StaticModint::new(self.val as u64 * rhs as u64)
    }

    #[inline]
    pub const fn div_raw(&self, rhs: u32) -> Self {
        debug_assert!(rhs < M::N);
        self.mul_raw(StaticModint::<M>::raw(rhs).inv().val)
    }
}

impl<M: Modulo> Default for StaticModint<M> {
    fn default() -> Self { StaticModint::zero() }
}

impl<M: Modulo> std::fmt::Debug for StaticModint<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.val) }
}

impl<M: Modulo> std::fmt::Display for StaticModint<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{}", self.val) }
}

impl<M: Modulo> Add for StaticModint<M> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output { self.add_raw(rhs.val) }
}

impl<M: Modulo> AddAssign for StaticModint<M> {
    fn add_assign(&mut self, rhs: Self) { *self = *self + rhs; }
}

impl<M: Modulo> Sub for StaticModint<M> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output { self.sub_raw(rhs.val) }
}

impl<M: Modulo> SubAssign for StaticModint<M> {
    fn sub_assign(&mut self, rhs: Self) { *self = *self - rhs; }
}

impl<M: Modulo> Mul for StaticModint<M> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output { self.mul_raw(rhs.val) }
}

impl<M: Modulo> MulAssign for StaticModint<M> {
    fn mul_assign(&mut self, rhs: Self) { *self = *self * rhs; }
}

impl<M: Modulo> Div for StaticModint<M> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        debug_assert!(rhs.val != 0);
        self * rhs.inv()
    }
}

impl<M: Modulo> DivAssign for StaticModint<M> {
    fn div_assign(&mut self, rhs: Self) {
        debug_assert!(rhs.val != 0);
        *self *= rhs.inv()
    }
}

impl<M: Modulo> From<u32> for StaticModint<M> {
    fn from(value: u32) -> Self { Self::new(value as u64) }
}

impl<M: Modulo> From<u64> for StaticModint<M> {
    fn from(value: u64) -> Self { Self::new(value) }
}

impl<M: Modulo> From<i32> for StaticModint<M> {
    fn from(value: i32) -> Self { Self::new_signed(value as i64) }
}

impl<M: Modulo> From<i64> for StaticModint<M> {
    fn from(value: i64) -> Self { Self::new_signed(value) }
}

pub fn combination<M: Modulo>(size: u32) -> impl Fn(u32, u32) -> StaticModint<M> {
    let mut fact = vec![StaticModint::<M>::one()];
    fact.append(
        &mut (1..=size)
            .scan(StaticModint::<M>::one(), |s, v| {
                *s *= StaticModint::new(v as u64);
                Some(*s)
            })
            .collect(),
    );

    let inv = fact[size as usize].inv();
    let mut ifact = vec![inv];
    ifact.append(
        &mut (1..=size)
            .rev()
            .scan(inv, |s, v| {
                *s *= StaticModint::new(v as u64);
                Some(*s)
            })
            .collect(),
    );
    ifact.reverse();

    move |n: u32, k: u32| {
        if n < k {
            StaticModint::zero()
        } else {
            fact[n as usize] * ifact[k as usize] * ifact[(n - k) as usize]
        }
    }
}
