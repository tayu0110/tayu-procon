use numeric::{Integer, One, Zero};
use std::marker;
use std::ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Sub, SubAssign};

pub trait Modulo<T = i64>: Clone + marker::Copy + PartialEq + Eq {
    fn modulo() -> T;
    fn primitive_root() -> T {
        unimplemented!()
    }
    fn montgomery_constant_mask() -> T {
        unimplemented!()
    }
    fn montgomery_constant_r() -> T {
        unimplemented!()
    }
    fn montgomery_constant_r_inv() -> T {
        unimplemented!()
    }
    fn montgomery_constant_r_pow2() -> T {
        unimplemented!()
    }
    fn montgomery_constant_modulo_inv() -> T {
        unimplemented!()
    }
}

#[derive(Clone, marker::Copy, PartialEq, Eq)]
pub enum Mod998244353<T = i64> {
    PhantomData(std::marker::PhantomData<T>),
}
impl Modulo for Mod998244353 {
    #[inline]
    fn modulo() -> i64 {
        998_244_353i64
    }
    #[inline]
    // R - 1 = 2^63 - 1
    fn montgomery_constant_mask() -> i64 {
        0x7FFFFFFFFFFFFFFF
    }
    #[inline]
    fn primitive_root() -> i64 {
        3i64
    }
    #[inline]
    // R = 2^63 mod 998244353
    fn montgomery_constant_r() -> i64 {
        466025955
    }
    #[inline]
    // R2 = 2^126 mod 998244353
    fn montgomery_constant_r_pow2() -> i64 {
        74890016
    }
    #[inline]
    // R^{-1} = (2^63 mod 998244353)^{-1} mod 998244353
    fn montgomery_constant_r_inv() -> i64 {
        890394177
    }
    #[inline]
    // modulo * modulo_inv = -1 mod R
    fn montgomery_constant_modulo_inv() -> i64 {
        8226880251553120255
    }
}

#[derive(Clone, marker::Copy, PartialEq, Eq)]
pub enum Mod1000000007 {}
impl Modulo for Mod1000000007 {
    #[inline]
    fn modulo() -> i64 {
        1_000_000_007i64
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Mint<M: Modulo> {
    val: i64,
    _p: marker::PhantomData<M>,
}

impl<M: Modulo> One for Mint<M> {
    #[inline]
    fn one() -> Self {
        Mint {
            val: 1i64,
            _p: marker::PhantomData,
        }
    }
}

impl<M: Modulo> Zero for Mint<M> {
    #[inline]
    fn zero() -> Self {
        Mint {
            val: 0i64,
            _p: marker::PhantomData,
        }
    }
}

impl<M: Modulo> Mint<M> {
    #[inline]
    pub fn new(val: i64) -> Self {
        Mint {
            val: (val % M::modulo() + M::modulo()) % M::modulo(),
            _p: marker::PhantomData,
        }
    }

    #[inline]
    pub fn raw(val: i64) -> Self {
        debug_assert!(0 <= val && val < M::modulo());
        Mint {
            val,
            _p: marker::PhantomData,
        }
    }

    #[inline]
    pub fn modulo() -> i64 {
        M::modulo()
    }

    #[inline]
    pub fn val(&self) -> i64 {
        self.val
    }

    pub fn pow(&self, mut exp: i64) -> Self {
        let (mut val, mut res) = (self.val, 1);
        while exp > 0 {
            if exp & 1 == 1 {
                res = (res * val) % M::modulo();
            }
            val = (val * val) % M::modulo();
            exp >>= 1;
        }
        Self {
            val: res,
            _p: marker::PhantomData,
        }
    }

    #[inline]
    pub fn inv(&self) -> Self {
        self.pow(M::modulo() - 2)
    }

    #[inline]
    pub fn nth_root(n: i64) -> Self {
        debug_assert!(n.abs() == 1 << n.abs().trailing_zeros());
        debug_assert!(M::modulo() - 1 + (M::modulo() - 1) / n >= 0);

        Mint::raw(M::primitive_root()).pow(M::modulo() - 1 + (M::modulo() - 1) / n)
    }

    #[inline]
    pub fn add_raw(&self, rhs: i64) -> Self {
        debug_assert!(0 <= rhs && rhs < M::modulo());
        Mint::new(self.val + rhs)
    }

    #[inline]
    pub fn sub_raw(&self, rhs: i64) -> Self {
        debug_assert!(0 <= rhs && rhs < M::modulo());
        Mint::new(self.val - rhs)
    }

    #[inline]
    pub fn mul_raw(&self, rhs: i64) -> Self {
        debug_assert!(0 <= rhs && rhs < M::modulo());
        Mint::new(self.val * rhs)
    }

    #[inline]
    pub fn div_raw(&self, rhs: i64) -> Self {
        debug_assert!(0 <= rhs && rhs < M::modulo());
        *self / Mint::raw(rhs)
    }
}

impl<M: Modulo> Default for Mint<M> {
    fn default() -> Self {
        Mint::zero()
    }
}

impl<M: Modulo> std::fmt::Debug for Mint<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl<M: Modulo> std::fmt::Display for Mint<M> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl<M: Modulo> Add for Mint<M> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.val + rhs.val)
    }
}

impl<M: Modulo> AddAssign for Mint<M> {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<M: Modulo> Sub for Mint<M> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(self.val - rhs.val + M::modulo())
    }
}

impl<M: Modulo> SubAssign for Mint<M> {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<M: Modulo> Mul for Mint<M> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.val * rhs.val)
    }
}

impl<M: Modulo> MulAssign for Mint<M> {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<M: Modulo> Div for Mint<M> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        debug_assert!(rhs.val != 0);
        self * rhs.inv()
    }
}

impl<M: Modulo> DivAssign for Mint<M> {
    fn div_assign(&mut self, rhs: Self) {
        debug_assert!(rhs.val != 0);
        *self *= rhs.inv()
    }
}

pub fn combination<M: Modulo>(size: i64) -> impl Fn(usize, usize) -> Mint<M> {
    let mut fact = vec![Mint::<M>::one()];
    fact.append(
        &mut (1..=size)
            .scan(Mint::<M>::one(), |s, v| {
                *s *= Mint::new(v);
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
                *s *= Mint::new(v);
                Some(*s)
            })
            .collect(),
    );
    ifact.reverse();

    move |n: usize, k: usize| {
        if n < k {
            Mint::zero()
        } else {
            fact[n] * ifact[k] * ifact[n - k]
        }
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// MontgomeryModint
////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub trait MontgomeryMultiplication<M: Modulo<T>, T> {
    // t <- MR(T) = (T + (TN' mod R) * N) / R
    //  if t >= N then return t - N else return t
    //      T := a (0 <= T < NR)
    //      N := modulo()
    //      N':= montgomery_constant_modulo_inv()
    //      R := montgomery_constant_r()
    fn montgomery_reduction(self) -> Self;
    fn multiplication(self, rhs: Self) -> Self;
}

impl<M: Modulo<u32>> MontgomeryMultiplication<M, u32> for u32 {
    #[inline]
    fn montgomery_reduction(self) -> u32 {
        let t = ((self as u64).wrapping_add(
            (self.wrapping_mul(M::montgomery_constant_modulo_inv()) as u64)
                .wrapping_mul(M::modulo() as u64),
        ) >> 32) as u32;
        if t >= M::modulo() {
            t - M::modulo()
        } else {
            t
        }
    }
    #[inline]
    fn multiplication(self, rhs: Self) -> Self {
        let a = self as u64 * rhs as u64;
        let t = (a.wrapping_add(
            ((a as u32).wrapping_mul(M::montgomery_constant_modulo_inv()) as u64)
                .wrapping_mul(M::modulo() as u64),
        ) >> 32) as u32;
        if t >= M::modulo() {
            t - M::modulo()
        } else {
            t
        }
    }
}

impl<M: Modulo> MontgomeryMultiplication<M, i64> for i64 {
    #[inline]
    fn montgomery_reduction(self) -> i64 {
        let t = ((self as i128).wrapping_add(
            ((self as i128).wrapping_mul(M::montgomery_constant_modulo_inv() as i128)
                & M::montgomery_constant_mask() as i128)
                .wrapping_mul(M::modulo() as i128),
        ) >> 63) as i64;
        if t >= M::modulo() {
            t - M::modulo()
        } else {
            t
        }
    }
    #[inline]
    fn multiplication(self, rhs: Self) -> Self {
        let a = self as i128 * rhs as i128;
        let t = (a.wrapping_add(
            (a.wrapping_mul(M::montgomery_constant_modulo_inv() as i128)
                & M::montgomery_constant_mask() as i128)
                .wrapping_mul(M::modulo() as i128),
        ) >> 63) as i64;
        if t >= M::modulo() {
            t - M::modulo()
        } else {
            t
        }
    }
}

impl Modulo<u32> for Mod998244353<u32> {
    #[inline]
    fn modulo() -> u32 {
        998_244_353u32
    }
    #[inline]
    // R - 1 = 2^32 - 1
    fn montgomery_constant_mask() -> u32 {
        !0
    }
    #[inline]
    // modulo * modulo_inv = -1 mod R
    fn montgomery_constant_modulo_inv() -> u32 {
        998244351
    }
    #[inline]
    // R = 2^32 mod 998244353
    fn montgomery_constant_r() -> u32 {
        301989884
    }
    #[inline]
    // R^{-1} = (2^32 mod 998244353)^{-1} mod 998244353
    fn montgomery_constant_r_inv() -> u32 {
        232013824
    }
    #[inline]
    // R2 = 2^64 mod 998244353
    fn montgomery_constant_r_pow2() -> u32 {
        932051910
    }
    #[inline]
    fn primitive_root() -> u32 {
        3
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct MontgomeryModint<M: Modulo<T>, T = i64> {
    val: T,
    _phantom: std::marker::PhantomData<M>,
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> MontgomeryModint<M, T> {
    #[inline]
    pub fn new(val: T) -> Self {
        let val = val.multiplication(M::montgomery_constant_r_pow2());
        Self {
            val,
            _phantom: std::marker::PhantomData,
        }
    }

    #[inline]
    pub fn val(&self) -> T {
        self.val.montgomery_reduction()
    }

    #[inline]
    pub fn val_montgomery_expression(&self) -> T {
        self.val
    }

    #[inline]
    pub fn one() -> Self {
        Self {
            val: M::montgomery_constant_r(),
            _phantom: std::marker::PhantomData,
        }
    }

    #[inline]
    pub fn zero() -> Self {
        Self {
            val: T::zero(),
            _phantom: std::marker::PhantomData,
        }
    }

    pub fn pow(&self, mut n: T) -> Self {
        let mut val = self.val;
        let mut res = if (n & T::one()) != T::zero() {
            val
        } else {
            M::montgomery_constant_r()
        };
        n >>= 1;
        while n != T::zero() {
            val = val.multiplication(val);
            if n & T::one() != T::zero() {
                res = res.multiplication(val);
            }
            n >>= 1;
        }
        Self {
            val: res,
            _phantom: std::marker::PhantomData,
        }
    }

    #[inline]
    pub fn nth_root(n: T) -> Self {
        debug_assert!(n == T::one() << n.trailing_zeros());
        debug_assert!(M::modulo() - T::one() + (M::modulo() - T::one()) / n >= T::zero());

        MontgomeryModint::<M, T>::new(M::primitive_root())
            .pow(M::modulo() - T::one() + (M::modulo() - T::one()) / n)
    }

    #[inline]
    pub fn inv(&self) -> Self {
        self.pow(M::modulo() - T::one() - T::one())
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> One for MontgomeryModint<M, T> {
    #[inline]
    fn one() -> Self {
        Self::one()
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> Zero for MontgomeryModint<M, T> {
    #[inline]
    fn zero() -> Self {
        Self::zero()
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> Add for MontgomeryModint<M, T> {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        let (t, fa) = self.val.overflowing_add(rhs.val);
        let (u, fs) = t.overflowing_sub(M::modulo());
        Self {
            val: if fa || !fs { u } else { t },
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> Sub for MontgomeryModint<M, T> {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        let (val, f) = self.val.overflowing_sub(rhs.val);
        Self {
            val: if f || val < T::zero() {
                val.wrapping_add(M::modulo())
            } else {
                val
            },
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> Mul for MontgomeryModint<M, T> {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self {
            val: self.val.multiplication(rhs.val),
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> Div for MontgomeryModint<M, T> {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        self * rhs.inv()
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> AddAssign
    for MontgomeryModint<M, T>
{
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> SubAssign
    for MontgomeryModint<M, T>
{
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> MulAssign
    for MontgomeryModint<M, T>
{
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> DivAssign
    for MontgomeryModint<M, T>
{
    fn div_assign(&mut self, rhs: Self) {
        *self = *self / rhs;
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> std::fmt::Debug
    for MontgomeryModint<M, T>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val())
    }
}

impl<M: Modulo<T>, T: Integer + MontgomeryMultiplication<M, T>> std::fmt::Display
    for MontgomeryModint<M, T>
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val())
    }
}

////////////////////////////////////////////////////////////////////////////////////////////////////////////
/// MontgomeryOperator
///   - Use Montgomery multiplication to reduce the cost of surplus multiplication.
///   - For implementation reasons, for now I limit modulo to odd numbers for now.
////////////////////////////////////////////////////////////////////////////////////////////////////////////
pub struct MontgomeryOperator {
    pub modulo: u64,
    pub inv_modulo: u64,
    pub r: u64,
    pub neg_r: u64,
    pub half_modulo: u64,
    pub r2: u64,
    pub d: u64,
}

impl MontgomeryOperator {
    pub const fn new(modulo: u64) -> Self {
        assert!(modulo & 1 != 0);

        let inv_modulo = {
            let mut i = 0;
            let mut inv_modulo = modulo;
            while i < 5 {
                inv_modulo =
                    inv_modulo.wrapping_mul(2u64.wrapping_sub(modulo.wrapping_mul(inv_modulo)));
                i += 1;
            }
            inv_modulo
        };

        let half_modulo = (modulo >> 1) + 1;
        let r = modulo.wrapping_neg() % modulo;
        let neg_r = modulo - r;
        let r2 = ((modulo as u128).wrapping_neg() % (modulo as u128)) as u64;
        let d = (modulo - 1) >> (modulo - 1).trailing_zeros();

        Self {
            modulo,
            inv_modulo,
            r,
            neg_r,
            half_modulo,
            r2,
            d,
        }
    }

    pub const fn add(&self, a: u64, b: u64) -> u64 {
        let (t, fa) = a.overflowing_add(b);
        let (u, fs) = t.overflowing_sub(self.modulo);
        if fa || !fs {
            u
        } else {
            t
        }
    }

    pub const fn sub(&self, a: u64, b: u64) -> u64 {
        let (t, f) = a.overflowing_sub(b);
        if f {
            t.wrapping_add(self.modulo)
        } else {
            t
        }
    }

    pub const fn div2(&self, ar: u64) -> u64 {
        if ar & 1 != 0 {
            (ar >> 1) + self.half_modulo
        } else {
            ar >> 1
        }
    }

    pub const fn mul(&self, ar: u64, br: u64) -> u64 {
        let t = (ar as u128) * (br as u128);
        let (t, f) = ((t >> 64) as u64).overflowing_sub(
            (((((t as u64).wrapping_mul(self.inv_modulo)) as u128) * self.modulo as u128) >> 64)
                as u64,
        );
        if f {
            t.wrapping_add(self.modulo)
        } else {
            t
        }
    }

    pub const fn mr(&self, ar: u64) -> u64 {
        let (t, f) =
            (((((ar.wrapping_mul(self.inv_modulo)) as u128) * (self.modulo as u128)) >> 64) as u64)
                .overflowing_neg();
        if f {
            t.wrapping_add(self.modulo)
        } else {
            t
        }
    }
    pub const fn ar(&self, a: u64) -> u64 {
        self.mul(a, self.r2)
    }

    pub const fn pow(&self, mut ar: u64, mut b: u64) -> u64 {
        let mut t = if (b & 1) != 0 { ar } else { self.r };
        b >>= 1;
        while b != 0 {
            ar = self.mul(ar, ar);
            if b & 1 != 0 {
                t = self.mul(t, ar);
            }
            b >>= 1;
        }
        t
    }
}

#[cfg(test)]
mod tests {
    use super::{combination, Mint, Mod1000000007, Mod998244353, Modulo, MontgomeryModint};
    use numeric::One;

    #[test]
    fn modint_test() {
        assert_eq!(Mod998244353::<i64>::modulo(), 998244353);
        assert_eq!(Mod1000000007::modulo(), 1000000007);

        const A: i64 = 347384953;
        const B: i64 = 847362948;
        let a = Mint::<Mod998244353>::raw(A);
        let b = Mint::<Mod998244353>::raw(B);
        assert_eq!((a + b).val(), 196503548);
        assert_eq!((a - b).val(), 498266358);
        assert_eq!((a * b).val(), 17486571);
        assert_eq!((a / b).val(), 748159151);
        assert_eq!(a.add_raw(B).val(), 196503548);
        assert_eq!(a.sub_raw(B).val(), 498266358);
        assert_eq!(a.mul_raw(B).val(), 17486571);
        assert_eq!(a.div_raw(B).val(), 748159151);
        assert_eq!(a.pow(B).val(), 860108694);
        assert_eq!(Mint::<Mod998244353>::nth_root(1 << 20).val(), 565042129);
        assert_eq!(Mint::<Mod998244353>::nth_root(4).pow(4), Mint::one());
    }

    #[test]
    fn combination_test() {
        const A: usize = 35;
        const CASE: [[i64; A + 1]; A + 1] = [
            [
                1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 2, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 3, 3, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 4, 6, 4, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 5, 10, 10, 5, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 6, 15, 20, 15, 6, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 7, 21, 35, 35, 21, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 8, 28, 56, 70, 56, 28, 8, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 9, 36, 84, 126, 126, 84, 36, 9, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 10, 45, 120, 210, 252, 210, 120, 45, 10, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 11, 55, 165, 330, 462, 462, 330, 165, 55, 11, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 12, 66, 220, 495, 792, 924, 792, 495, 220, 66, 12, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 13, 78, 286, 715, 1287, 1716, 1716, 1287, 715, 286, 78, 13, 1, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 14, 91, 364, 1001, 2002, 3003, 3432, 3003, 2002, 1001, 364, 91, 14, 1, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 15, 105, 455, 1365, 3003, 5005, 6435, 6435, 5005, 3003, 1365, 455, 105, 15, 1,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 16, 120, 560, 1820, 4368, 8008, 11440, 12870, 11440, 8008, 4368, 1820, 560, 120,
                16, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 17, 136, 680, 2380, 6188, 12376, 19448, 24310, 24310, 19448, 12376, 6188, 2380,
                680, 136, 17, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 18, 153, 816, 3060, 8568, 18564, 31824, 43758, 48620, 43758, 31824, 18564, 8568,
                3060, 816, 153, 18, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 19, 171, 969, 3876, 11628, 27132, 50388, 75582, 92378, 92378, 75582, 50388,
                27132, 11628, 3876, 969, 171, 19, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0,
            ],
            [
                1, 20, 190, 1140, 4845, 15504, 38760, 77520, 125970, 167960, 184756, 167960,
                125970, 77520, 38760, 15504, 4845, 1140, 190, 20, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0,
            ],
            [
                1, 21, 210, 1330, 5985, 20349, 54264, 116280, 203490, 293930, 352716, 352716,
                293930, 203490, 116280, 54264, 20349, 5985, 1330, 210, 21, 1, 0, 0, 0, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 22, 231, 1540, 7315, 26334, 74613, 170544, 319770, 497420, 646646, 705432,
                646646, 497420, 319770, 170544, 74613, 26334, 7315, 1540, 231, 22, 1, 0, 0, 0, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 23, 253, 1771, 8855, 33649, 100947, 245157, 490314, 817190, 1144066, 1352078,
                1352078, 1144066, 817190, 490314, 245157, 100947, 33649, 8855, 1771, 253, 23, 1, 0,
                0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 24, 276, 2024, 10626, 42504, 134596, 346104, 735471, 1307504, 1961256, 2496144,
                2704156, 2496144, 1961256, 1307504, 735471, 346104, 134596, 42504, 10626, 2024,
                276, 24, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 25, 300, 2300, 12650, 53130, 177100, 480700, 1081575, 2042975, 3268760, 4457400,
                5200300, 5200300, 4457400, 3268760, 2042975, 1081575, 480700, 177100, 53130, 12650,
                2300, 300, 25, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 26, 325, 2600, 14950, 65780, 230230, 657800, 1562275, 3124550, 5311735, 7726160,
                9657700, 10400600, 9657700, 7726160, 5311735, 3124550, 1562275, 657800, 230230,
                65780, 14950, 2600, 325, 26, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 27, 351, 2925, 17550, 80730, 296010, 888030, 2220075, 4686825, 8436285,
                13037895, 17383860, 20058300, 20058300, 17383860, 13037895, 8436285, 4686825,
                2220075, 888030, 296010, 80730, 17550, 2925, 351, 27, 1, 0, 0, 0, 0, 0, 0, 0, 0,
            ],
            [
                1, 28, 378, 3276, 20475, 98280, 376740, 1184040, 3108105, 6906900, 13123110,
                21474180, 30421755, 37442160, 40116600, 37442160, 30421755, 21474180, 13123110,
                6906900, 3108105, 1184040, 376740, 98280, 20475, 3276, 378, 28, 1, 0, 0, 0, 0, 0,
                0, 0,
            ],
            [
                1, 29, 406, 3654, 23751, 118755, 475020, 1560780, 4292145, 10015005, 20030010,
                34597290, 51895935, 67863915, 77558760, 77558760, 67863915, 51895935, 34597290,
                20030010, 10015005, 4292145, 1560780, 475020, 118755, 23751, 3654, 406, 29, 1, 0,
                0, 0, 0, 0, 0,
            ],
            [
                1, 30, 435, 4060, 27405, 142506, 593775, 2035800, 5852925, 14307150, 30045015,
                54627300, 86493225, 119759850, 145422675, 155117520, 145422675, 119759850,
                86493225, 54627300, 30045015, 14307150, 5852925, 2035800, 593775, 142506, 27405,
                4060, 435, 30, 1, 0, 0, 0, 0, 0,
            ],
            [
                1, 31, 465, 4495, 31465, 169911, 736281, 2629575, 7888725, 20160075, 44352165,
                84672315, 141120525, 206253075, 265182525, 300540195, 300540195, 265182525,
                206253075, 141120525, 84672315, 44352165, 20160075, 7888725, 2629575, 736281,
                169911, 31465, 4495, 465, 31, 1, 0, 0, 0, 0,
            ],
            [
                1, 32, 496, 4960, 35960, 201376, 906192, 3365856, 10518300, 28048800, 64512240,
                129024480, 225792840, 347373600, 471435600, 565722720, 601080390, 565722720,
                471435600, 347373600, 225792840, 129024480, 64512240, 28048800, 10518300, 3365856,
                906192, 201376, 35960, 4960, 496, 32, 1, 0, 0, 0,
            ],
            [
                1, 33, 528, 5456, 40920, 237336, 1107568, 4272048, 13884156, 38567100, 92561040,
                193536720, 354817320, 573166440, 818809200, 38913967, 168558757, 168558757,
                38913967, 818809200, 573166440, 354817320, 193536720, 92561040, 38567100, 13884156,
                4272048, 1107568, 237336, 40920, 5456, 528, 33, 1, 0, 0,
            ],
            [
                1, 34, 561, 5984, 46376, 278256, 1344904, 5379616, 18156204, 52451256, 131128140,
                286097760, 548354040, 927983760, 393731287, 857723167, 207472724, 337117514,
                207472724, 857723167, 393731287, 927983760, 548354040, 286097760, 131128140,
                52451256, 18156204, 5379616, 1344904, 278256, 46376, 5984, 561, 34, 1, 0,
            ],
            [
                1, 35, 595, 6545, 52360, 324632, 1623160, 6724520, 23535820, 70607460, 183579396,
                417225900, 834451800, 478093447, 323470694, 253210101, 66951538, 544590238,
                544590238, 66951538, 253210101, 323470694, 478093447, 834451800, 417225900,
                183579396, 70607460, 23535820, 6724520, 1623160, 324632, 52360, 6545, 595, 35, 1,
            ],
        ];

        let com = combination::<Mod998244353>(A as i64);
        for n in 0..=A {
            for k in 0..=A {
                assert_eq!(com(n, k).val(), CASE[n][k]);
            }
        }
    }

    #[test]
    fn montgomery_modint_test() {
        type Modint = MontgomeryModint<Mod998244353>;

        assert_eq!(Modint::zero().val(), 0);
        assert_eq!(Modint::one().val(), 1);
        assert_eq!(Modint::new(10).val(), 10);

        const A: i64 = 347384953;
        const B: i64 = 847362948;
        let a = Modint::new(A);
        let b = Modint::new(B);
        assert_eq!((a + b).val(), 196503548);
        assert_eq!((a - b).val(), 498266358);
        assert_eq!((a * b).val(), 17486571);
        assert_eq!(a.pow(B).val(), 860108694);
        assert_eq!((a / b).val(), 748159151);
    }

    #[test]
    fn montgomery_modint_u32_test() {
        type Modint = MontgomeryModint<Mod998244353<u32>, u32>;

        assert_eq!(Modint::zero().val(), 0);
        assert_eq!(Modint::one().val(), 1);
        assert_eq!(Modint::new(10).val(), 10);

        const A: u32 = 347384953;
        const B: u32 = 847362948;
        let a = Modint::new(A);
        let b = Modint::new(B);
        assert_eq!((a + b).val(), 196503548);
        assert_eq!((a - b).val(), 498266358);
        assert_eq!((a * b).val(), 17486571);
        assert_eq!(a.pow(B).val(), 860108694);
        assert_eq!((a / b).val(), 748159151);
    }
}
