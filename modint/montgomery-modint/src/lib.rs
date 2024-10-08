mod simd;

use std::hash::Hash;
use std::marker::PhantomData;
use std::num::ParseIntError;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign};
use std::str::FromStr;

#[cfg(feature = "iolib")]
use iolib::{FastInput, Readable};
pub use modint_common::*;
pub use simd::*;
use simple_rand::xor_shift32;
use zero_one::{One, Zero};

////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// MontgomeryModint
////////////////////////////////////////////////////////////////////////////////////////////////////////////

#[derive(Clone, Copy, Eq)]
pub struct MontgomeryModint<M: Modulo> {
    pub val: u32,
    _phantom: PhantomData<fn() -> M>,
}

impl<M: Modulo> MontgomeryModint<M> {
    #[inline]
    pub const fn new(val: u32) -> Self {
        Self { val: mmul::<M>(val, M::R2), _phantom: PhantomData }
    }

    #[inline(always)]
    pub const fn from_rawval(val: u32) -> Self {
        Self { val, _phantom: PhantomData }
    }

    #[inline]
    pub const fn val(&self) -> u32 {
        mrestore::<M>(mreduce::<M>(self.val))
    }

    #[inline(always)]
    pub const fn rawval(&self) -> u32 {
        self.val
    }

    #[inline(always)]
    pub const fn one() -> Self {
        Self { val: M::R, _phantom: PhantomData }
    }

    #[inline(always)]
    pub const fn zero() -> Self {
        Self { val: 0, _phantom: PhantomData }
    }

    pub const fn pow(&self, mut n: u64) -> Self {
        let mut val = self.val;
        let mut res = M::R;
        while n != 0 {
            if n & 1 != 0 {
                res = mmul::<M>(res, val);
            }
            val = mmul::<M>(val, val);
            n >>= 1;
        }
        Self { val: res, _phantom: PhantomData }
    }

    #[inline]
    pub const fn nth_root(n: u32) -> Self {
        debug_assert!(n == 1 << n.trailing_zeros());
        MontgomeryModint::<M>::new(M::PRIM_ROOT).pow(M::N as u64 - 1 + (M::N as u64 - 1) / n as u64)
    }

    #[inline(always)]
    pub const fn inv(&self) -> Self {
        self.pow(M::N as u64 - 2)
    }

    pub fn sqrt(self) -> Option<Self> {
        if self == Self::zero() {
            Some(Self::zero())
        } else if self.pow(M::N as u64 >> 1) != Self::one() {
            None
        } else if M::N & 0b11 == 3 {
            let s = self.pow((M::N as u64 + 1) >> 2);
            let t = -s;
            Some(if s.val() < t.val() { s } else { t })
        } else {
            for b in xor_shift32(381928476372819).map(|v| v % (M::N - 2) + 2) {
                let b = Self::new(b);
                if b.pow((M::N as u64 - 1) >> 1) != Self::one() {
                    let q = (M::N - 1).trailing_zeros() as u64;
                    let s = (M::N - 1) >> q;

                    let mut x = self.pow((s as u64 + 1) >> 1);
                    let mut x2 = x * x;
                    let mut b = b.pow(s as u64);
                    let mninv = self.inv();

                    let mut shift = 2;
                    while x2 != self {
                        let diff = mninv * x2;
                        if diff.pow(1 << (q - shift)) != Self::one() {
                            x *= b;
                            b *= b;
                            x2 *= b;
                        } else {
                            b *= b;
                        }
                        shift += 1;
                    }
                    return Some(x);
                }
            }
            None // in this branch, sqrt of self must be found. so this point is unreachable
        }
    }

    #[inline]
    pub const fn add_const(self, rhs: Self) -> Self {
        MontgomeryModint { val: madd::<M>(self.val, rhs.val), _phantom: PhantomData }
    }

    #[inline]
    pub const fn sub_const(self, rhs: Self) -> Self {
        MontgomeryModint { val: msub::<M>(self.val, rhs.val), _phantom: PhantomData }
    }

    #[inline]
    pub const fn mul_const(self, rhs: Self) -> Self {
        MontgomeryModint { val: mmul::<M>(self.val, rhs.val), _phantom: PhantomData }
    }

    #[inline]
    pub const fn div_const(self, rhs: Self) -> Self {
        MontgomeryModint { val: self.mul_const(rhs.inv()).val, _phantom: PhantomData }
    }
}

impl<M: Modulo> One for MontgomeryModint<M> {
    #[inline]
    fn one() -> Self {
        Self::one()
    }
}

impl<M: Modulo> Zero for MontgomeryModint<M> {
    #[inline]
    fn zero() -> Self {
        Self::zero()
    }
}

impl<M: Modulo> Add for MontgomeryModint<M> {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self::Output {
        self.add_const(rhs)
    }
}

impl<M: Modulo> Sub for MontgomeryModint<M> {
    type Output = Self;
    #[inline(always)]
    fn sub(self, rhs: Self) -> Self::Output {
        self.sub_const(rhs)
    }
}

impl<M: Modulo> Mul for MontgomeryModint<M> {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self::Output {
        self.mul_const(rhs)
    }
}

impl<M: Modulo> Div for MontgomeryModint<M> {
    type Output = Self;
    #[inline(always)]
    fn div(self, rhs: Self) -> Self::Output {
        self.div_const(rhs)
    }
}

impl<M: Modulo> Neg for MontgomeryModint<M> {
    type Output = Self;
    fn neg(self) -> Self::Output {
        if self.val == 0 {
            self
        } else {
            Self { val: (M::N << 1) - self.val, _phantom: PhantomData }
        }
    }
}

impl<M: Modulo> PartialEq for MontgomeryModint<M> {
    fn eq(&self, other: &Self) -> bool {
        mrestore::<M>(self.val) == mrestore::<M>(other.val)
    }
}

impl<M: Modulo> AddAssign for MontgomeryModint<M> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<M: Modulo> SubAssign for MontgomeryModint<M> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<M: Modulo> MulAssign for MontgomeryModint<M> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<M: Modulo> DivAssign for MontgomeryModint<M> {
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl<M: Modulo> std::fmt::Debug for MontgomeryModint<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val())
    }
}

impl<M: Modulo> std::fmt::Display for MontgomeryModint<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val())
    }
}

impl<M: Modulo> From<u32> for MontgomeryModint<M> {
    fn from(value: u32) -> Self {
        Self::new(value)
    }
}

impl<M: Modulo> From<u64> for MontgomeryModint<M> {
    fn from(value: u64) -> Self {
        Self::new(value.rem_euclid(M::N as u64) as u32)
    }
}

impl<M: Modulo> From<i32> for MontgomeryModint<M> {
    fn from(value: i32) -> Self {
        Self::new(value.rem_euclid(M::N as i32) as u32)
    }
}

impl<M: Modulo> From<i64> for MontgomeryModint<M> {
    fn from(value: i64) -> Self {
        Self::new(value.rem_euclid(M::N as i64) as u32)
    }
}

impl<M: Modulo> FromStr for MontgomeryModint<M> {
    type Err = ParseIntError;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let neg = s.starts_with('-');

        let val = if neg {
            s[1..].bytes().fold(0u64, |s, v| s * 10 + (v - b'0') as u64)
        } else {
            s.bytes().fold(0u64, |s, v| s * 10 + (v - b'0') as u64)
        };

        if !neg && val < M::N as u64 {
            Ok(Self::new(val as u32))
        } else if neg {
            Ok(Self::from(-(val as i64)))
        } else {
            Ok(Self::from(val))
        }
    }
}

impl<M: Modulo> Hash for MontgomeryModint<M> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        mrestore::<M>(self.val).hash(state)
    }
}

#[cfg(feature = "iolib")]
impl<M: Modulo> Readable for MontgomeryModint<M> {
    fn read(src: &mut FastInput) -> Self {
        MontgomeryModint::from(u32::read(src))
    }
}

#[cfg(test)]
mod tests {
    use std::time::{SystemTime, UNIX_EPOCH};

    use super::*;
    use modint_common::{Mod4194304001, Mod998244353, Modulo};

    #[test]
    fn constant_value_test() {
        assert_eq!(Mod998244353::N, 998244353);
        assert_eq!(Mod998244353::R, 301989884);
        assert_eq!(Mod998244353::R2, 932051910);
        assert_eq!(Mod998244353::PRIM_ROOT, 3);
    }

    #[test]
    fn montgomery_modint_test() {
        type Modint = MontgomeryModint<Mod998244353>;

        assert_eq!(Mod998244353::R, 301989884);
        assert_eq!(Mod998244353::R2, 932051910);

        assert_eq!(Modint::zero().val(), 0);
        assert_eq!(Modint::one().val(), 1);
        assert_eq!(Modint::new(10).val(), 10);

        const A: u32 = 347384953;
        const B: u32 = 847362948;
        let a = Modint::new(A);
        let b = Modint::new(B);
        assert_eq!((a + b).val(), 196503548);
        assert_eq!((a - b).val(), 498266358);
        assert_eq!(
            (a * b).val(),
            (A as u64 * B as u64 % Mod998244353::N as u64) as u32
        );
        assert_eq!(a.pow(B as u64).val(), 860108694);
        assert_eq!((a / b).val(), 748159151);
        assert_eq!((-a).val(), (Modint::zero() - a).val());

        assert_eq!("347384953".parse::<Modint>(), Ok(Modint::new(347384953)));
        assert_eq!(
            "-347384953".parse::<Modint>(),
            Ok(Modint::from(-347384953i64))
        );
    }

    #[test]
    fn montgomery_modint_large_mod_test() {
        type Modint = MontgomeryModint<Mod4194304001>;

        assert_eq!(Modint::zero().val(), 0u32);
        assert_eq!(Modint::one().val(), 1u32);
        assert_eq!(Modint::new(10).val(), 10u32);

        const A: u32 = 347384953;
        const B: u32 = 847362948;
        let a = Modint::new(A);
        let b = Modint::new(B);
        assert_eq!((a + b).val(), 1194747901u32);
        assert_eq!((a - b).val(), 3694326006u32);
        assert_eq!(
            (a * b).val(),
            (A as u64 * B as u64 % Mod4194304001::N as u64) as u32
        );
        assert_eq!(a.pow(B as u64).val(), 101451096u32);
        assert_eq!((a / b).val(), 3072607503);
    }

    #[test]
    fn mod_sqrt_test() {
        for n in xor_shift32(
            SystemTime::now()
                .duration_since(UNIX_EPOCH)
                .unwrap()
                .as_secs(),
        )
        .take(10000)
        {
            let sq = (n as u64 * n as u64 % Mod998244353::N as u64) as u32;
            let sq = MontgomeryModint::<Mod998244353>::new(sq);
            let sqrt = sq.sqrt();
            assert!(sqrt.is_some());
            assert_eq!(sqrt.unwrap() * sqrt.unwrap(), sq);
        }
    }
}
