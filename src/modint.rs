use std::marker;
use std::ops::{
    Add,
    AddAssign,
    Sub,
    SubAssign,
    Mul,
    MulAssign,
    Div,
    DivAssign
};

pub trait Modulo: marker::Copy + PartialEq + Eq {
    fn modulo() -> i64;
    fn primitive_root() -> i64;
}

#[derive(Clone, marker::Copy, PartialEq, Eq)]
pub enum Mod998244353 {}
impl Modulo for Mod998244353 {
    fn modulo() -> i64 { 998_244_353i64 }
    fn primitive_root() -> i64 { 3i64 }
}

#[derive(Clone, marker::Copy, PartialEq, Eq)]
pub enum Mod1000000007 {}
impl Modulo for Mod1000000007 {
    fn modulo() -> i64 { 1_000_000_007i64 }
    fn primitive_root() -> i64 { unimplemented!(); }
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Mint<M>
where M: Modulo {
    val: i64,
    _p: marker::PhantomData<M>
}

#[allow(dead_code)]
impl<M> Mint<M>
where M: Modulo {
    pub fn new(val: i64) -> Self {
        Mint {
            val: (val % M::modulo() + M::modulo()) % M::modulo(),
            _p: marker::PhantomData
        }
    }
    
    pub fn raw(val: i64) -> Self {
        assert!(0 <= val && val < M::modulo());
        Mint {
            val,
            _p: marker::PhantomData
        }
    }
    
    pub fn zero() -> Self {
        Mint {
            val: 0i64,
            _p: marker::PhantomData
        }
    }
    
    pub fn one() -> Self {
        Mint {
            val: 1i64,
            _p: marker::PhantomData
        }
    }
    
    pub fn modulo() -> i64 {
        M::modulo()
    }
    
    pub fn val(&self) -> i64 {
        self.val
    }
    
    pub fn pow(&self, mut exp: i64) -> Self {
        let (mut val, mut res) = (self.val, 1);
        while exp > 0 {
            if exp % 2 == 1 { 
                res = (res * val) % M::modulo();
            }
            val = (val * val) % M::modulo();
            exp >>= 1;
        }
        Self {
            val: res,
            _p: marker::PhantomData
        }
    }

    pub fn inv(&self) -> Self {
        self.pow(M::modulo() - 2)
    }
    
    pub fn nth_root(n: i64) -> Self {
        assert!(n.abs() == 1 << n.abs().trailing_zeros());
        assert!(M::modulo() - 1 + (M::modulo() - 1) / n >= 0);

        Mint::raw(M::primitive_root()).pow(M::modulo() - 1 + (M::modulo() - 1) / n)
    }
    
    pub fn add_raw(&self, rhs: i64) -> Self {
        *self + Mint::new(rhs)
    }
    
    pub fn sub_raw(&self, rhs: i64) -> Self {
        *self - Mint::new(rhs)
    }
    
    pub fn mul_raw(&self, rhs: i64) -> Self {
        *self * Mint::new(rhs)
    }
    
    pub fn div_raw(&self, rhs: i64) -> Self {
        *self / Mint::new(rhs)
    }
}

impl<M> Default for Mint<M>
where M: Modulo {
    fn default() -> Self {
        Mint::zero()
    }
}

impl<M> std::fmt::Debug for Mint<M>
where M: Modulo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl<M> std::fmt::Display for Mint<M>
where M: Modulo {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.val)
    }
}

impl<M> Add for Mint<M>
where M: Modulo {
    type Output = Self;
    fn add(self, rhs: Self) -> Self::Output {
        Self::new(self.val + rhs.val)
    }
}

impl<M> AddAssign for Mint<M>
where M: Modulo {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl<M> Sub for Mint<M>
where M: Modulo {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self::Output {
        Self::new(self.val - rhs.val + M::modulo())
    }
}

impl<M> SubAssign for Mint<M>
where M: Modulo {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl<M> Mul for Mint<M>
where M: Modulo {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self::Output {
        Self::new(self.val * rhs.val)
    }
}

impl<M> MulAssign for Mint<M>
where M: Modulo {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl<M> Div for Mint<M>
where M: Modulo {
    type Output = Self;
    fn div(self, rhs: Self) -> Self::Output {
        assert!(rhs.val != 0);
        self * rhs.inv()
    }
}

impl<M> DivAssign for Mint<M>
where M: Modulo {
    fn div_assign(&mut self, rhs: Self) {
        assert!(rhs.val != 0);
        *self *= rhs.inv()
    }
}

pub struct Combination<M>
where M: Modulo {
    fact: Vec<Mint<M>>,
    ifact: Vec<Mint<M>>
}

#[allow(dead_code)]
impl<M> Combination<M>
where M: Modulo {
    pub fn new(size: usize) -> Self {
        let mut fact = vec![Mint::one(); size+1];
        let mut ifact = vec![Mint::one(); size+1];
        let mut buf = vec![Mint::one(); size+1];

        fact
            .iter_mut()
            .enumerate()
            .skip(1)
            .for_each(|(i, v)| {
                *v = buf[i-1] * Mint::raw(i as i64);
                buf[i] = *v;
            });
        
        ifact[size] = fact[size].inv();
        buf[size] = ifact[size];
        
        ifact
            .iter_mut()
            .enumerate()
            .skip(1)
            .rev()
            .skip(1)
            .for_each(|(i, v)| {
                *v = buf[i+1] * Mint::raw(i as i64 + 1);
                buf[i] = *v;
            });
        
            Self {
            fact,
            ifact
        }
    }

    pub fn get(&self, n: usize, k: usize) -> Mint<M> {
        if n < k {
            Mint::zero()
        } else {
            self.fact[n] * self.ifact[k] * self.ifact[n-k]
        }
    }
}

#[cfg(test)]
mod tests {
    use super::super::modint::{
        Mint, Combination,
        Mod998244353, Mod1000000007,
        Modulo
    };

    #[test]
    fn modint_test() {
        assert_eq!(Mod998244353::modulo(),                          998244353);
        assert_eq!(Mod1000000007::modulo(),                         1000000007);

        const A: i64 = 347384953;
        const B: i64 = 847362948;
        let a = Mint::<Mod998244353>::raw(A);
        let b = Mint::<Mod998244353>::raw(B);
        assert_eq!((a + b).val(),                                   196503548);
        assert_eq!((a - b).val(),                                   498266358);
        assert_eq!((a * b).val(),                                   17486571);
        assert_eq!((a / b).val(),                                   748159151);
        assert_eq!(a.add_raw(B).val(),                              196503548);
        assert_eq!(a.sub_raw(B).val(),                              498266358);
        assert_eq!(a.mul_raw(B).val(),                              17486571);
        assert_eq!(a.div_raw(B).val(),                              748159151);
        assert_eq!(a.pow(B).val(),                                  860108694);
        assert_eq!(Mint::<Mod998244353>::nth_root(1 << 20).val(),   565042129);
    }

    #[test]
    fn combination_test() {
        const A: usize = 20;
        const CASE: [[i64; A+1]; A+1] = [
            [1, 0,  0,   0,    0,    0,     0,     0,     0,      0,      0,      0,      0,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 1,  0,   0,    0,    0,     0,     0,     0,      0,      0,      0,      0,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 2,  1,   0,    0,    0,     0,     0,     0,      0,      0,      0,      0,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 3,  3,   1,    0,    0,     0,     0,     0,      0,      0,      0,      0,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 4,  6,   4,    1,    0,     0,     0,     0,      0,      0,      0,      0,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 5,  10,  10,   5,    1,     0,     0,     0,      0,      0,      0,      0,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 6,  15,  20,   15,   6,     1,     0,     0,      0,      0,      0,      0,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 7,  21,  35,   35,   21,    7,     1,     0,      0,      0,      0,      0,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 8,  28,  56,   70,   56,    28,    8,     1,      0,      0,      0,      0,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 9,  36,  84,   126,  126,   84,    36,    9,      1,      0,      0,      0,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 10, 45,  120,  210,  252,   210,   120,   45,     10,     1,      0,      0,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 11, 55,  165,  330,  462,   462,   330,   165,    55,     11,     1,      0,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 12, 66,  220,  495,  792,   924,   792,   495,    220,    66,     12,     1,      0,     0,     0,     0,    0,    0,   0,  0],
            [1, 13, 78,  286,  715,  1287,  1716,  1716,  1287,   715,    286,    78,     13,     1,     0,     0,     0,    0,    0,   0,  0],
            [1, 14, 91,  364,  1001, 2002,  3003,  3432,  3003,   2002,   1001,   364,    91,     14,    1,     0,     0,    0,    0,   0,  0],
            [1, 15, 105, 455,  1365, 3003,  5005,  6435,  6435,   5005,   3003,   1365,   455,    105,   15,    1,     0,    0,    0,   0,  0],
            [1, 16, 120, 560,  1820, 4368,  8008,  11440, 12870,  11440,  8008,   4368,   1820,   560,   120,   16,    1,    0,    0,   0,  0],
            [1, 17, 136, 680,  2380, 6188,  12376, 19448, 24310,  24310,  19448,  12376,  6188,   2380,  680,   136,   17,   1,    0,   0,  0],
            [1, 18, 153, 816,  3060, 8568,  18564, 31824, 43758,  48620,  43758,  31824,  18564,  8568,  3060,  816,   153,  18,   1,   0,  0],
            [1, 19, 171, 969,  3876, 11628, 27132, 50388, 75582,  92378,  92378,  75582,  50388,  27132, 11628, 3876,  969,  171,  19,  1,  0],
            [1, 20, 190, 1140, 4845, 15504, 38760, 77520, 125970, 167960, 184756, 167960, 125970, 77520, 38760, 15504, 4845, 1140, 190, 20, 1]
        ];

        let com = Combination::<Mod998244353>::new(A);
        for n in 0..=A {
            for k in 0..=A {
                assert_eq!(com.get(n, k).val(), CASE[n][k]);
            }
        }
    }

}
