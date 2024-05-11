mod dynamic;
mod fixed;
mod pointset;
mod splay;

pub use dynamic::*;
pub use fixed::*;
pub use pointset::*;
use splay::*;

use simple_rand::{gen_seed, xor_shift};
use std::ops::{Add, Index};
use std::sync::Mutex;

const CHARS: u64 = 1 << 8;
const MOD: u64 = (1 << 61) - 1;
const RT: u64 = 37;

fn mul(a: u64, b: u64) -> u64 {
    let t = a as u128 * b as u128;
    let t = (t >> 61) as u64 + (t as u64 & MOD);
    t - (MOD & ((t >= MOD) as u64).wrapping_neg())
}

fn mod_pow(a: u64, mut n: u64) -> u64 {
    let (mut res, mut pow) = (1, a);
    while n != 0 {
        if n & 1 != 0 {
            res = mul(res, pow);
        }
        pow = mul(pow, pow);
        n >>= 1;
    }
    res
}

fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b > 0 {
        a %= b;
        (a, b) = (b, a);
    }
    a
}

fn get_rand() -> u64 {
    xor_shift(gen_seed())
        .find(|&ns| gcd(ns, MOD - 1) == 1)
        .unwrap()
}

fn init_base() -> u64 {
    loop {
        let res = mod_pow(RT, get_rand());
        if res > CHARS {
            break res;
        }
    }
}

struct PowCache {
    base: u64,
    cache: Vec<u64>,
}

impl PowCache {
    const fn new() -> Self {
        Self { base: 0, cache: vec![] }
    }

    fn base(&mut self) -> u64 {
        if self.base == 0 {
            self.base = init_base();
        }
        self.base
    }

    fn grow(&mut self, size: usize) {
        let mut oldsize = self.cache.len();

        if size < oldsize {
            return;
        }

        let size = size.next_power_of_two();
        self.cache.resize(size + 1, 0);

        if oldsize == 0 {
            self.cache[0] = 1;
            oldsize += 1;
        }
        let base = self.base();
        for i in oldsize..size + 1 {
            self.cache[i] = mul(self.cache[i - 1], base);
        }
    }
}

impl Index<usize> for PowCache {
    type Output = u64;
    fn index(&self, index: usize) -> &Self::Output {
        &self.cache[index]
    }
}

static POW_CACHE: Mutex<PowCache> = Mutex::new(PowCache::new());

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct HashValue {
    len: usize,
    hash: u64,
}

impl HashValue {
    fn new(len: usize, hash: u64) -> Self {
        Self { len, hash }
    }

    /// Concat two `HashValue`.  
    ///
    /// If `l` represents the substring `s` and `r` represents the substring `t`,  
    /// then you can obtain the HashValue of the concatenated string of `s` and `t`.  
    ///
    /// # Example
    /// ```rust
    /// use string::RollingHash;
    ///
    /// let s = "abcdefgh";
    /// let hash = RollingHash::new(s);
    ///
    /// let sub = "abcfgh";
    /// let sub_hash = RollingHash::new(sub);
    ///
    /// assert_eq!(hash.get(..3).concat(hash.get(5..)), sub_hash.get(..));
    /// // std::ops::Add is implemented for HashValue. This is equivalent HashValue::concat.
    /// assert_eq!(hash.get(..3) + hash.get(5..), sub_hash.get(..));
    /// ```
    pub fn concat(self, rhs: HashValue) -> Self {
        let mut cache = POW_CACHE.lock().unwrap();
        cache.grow(rhs.len);
        let res = mul(self.hash, cache[rhs.len]) + rhs.hash;
        Self {
            len: self.len + rhs.len,
            hash: res - (((res >= MOD) as u64).wrapping_neg() & MOD),
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn raw_value(&self) -> u64 {
        self.hash
    }
}

impl Add for HashValue {
    type Output = HashValue;
    fn add(self, rhs: Self) -> Self::Output {
        self.concat(rhs)
    }
}
