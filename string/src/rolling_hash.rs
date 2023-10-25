use simple_rand::{gen_seed, xor_shift};
use std::ops::{Add, Bound, Index, Range, RangeBounds};
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
        .skip_while(|&ns| gcd(ns, MOD - 1) != 1)
        .next()
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
    const fn new() -> Self { Self { base: 0, cache: vec![] } }

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
    fn index(&self, index: usize) -> &Self::Output { &self.cache[index] }
}

static POW_CACHE: Mutex<PowCache> = Mutex::new(PowCache::new());

pub struct RollingHash {
    hash: Box<[u64]>,
}

impl RollingHash {
    /// Generate the rolling hash for a string `s`.
    #[inline]
    pub fn new(s: &str) -> Self {
        let mut cache = POW_CACHE.lock().unwrap();
        cache.grow(s.len());
        let mut hash = vec![0; s.len() + 1];

        let base = cache.base();
        for (i, c) in s.bytes().enumerate() {
            hash[i + 1] = c as u64 + mul(hash[i], base);
            if hash[i + 1] >= MOD {
                hash[i + 1] -= MOD;
            }
        }

        Self { hash: hash.into_boxed_slice() }
    }

    fn convert_range(&self, range: impl RangeBounds<usize>) -> Range<usize> {
        let l = match range.start_bound() {
            Bound::Included(l) => *l,
            Bound::Unbounded => 0,
            _ => unreachable!(),
        };
        let r = match range.end_bound() {
            Bound::Included(r) => r + 1,
            Bound::Excluded(r) => *r,
            // This is correct because the length of self.hash is 1 larger than the original string.
            Bound::Unbounded => self.hash.len() - 1,
        };
        Range { start: l, end: r }
    }

    /// Get the hash value of substring of `s` that you use generating RollingHash::new().
    ///
    /// # Example
    /// ```rust
    /// use string::RollingHash;
    ///
    /// let s = "abdabfgdabfgda";
    /// let hash = RollingHash::new(s);
    ///
    /// // you can use RangeTo, Range,
    /// assert_eq!(hash.get(..2), hash.get(3..5));
    /// // RangeInclusive, RangeFrom,
    /// assert_eq!(hash.get(3..=8), hash.get(8..));
    /// // RangeFull, and so on
    /// assert_ne!(hash.get(..), hash.get(..=5));
    /// ```
    #[inline]
    pub fn get(&self, range: impl RangeBounds<usize>) -> HashValue {
        let range = self.convert_range(range);

        if range.is_empty() {
            return HashValue::new(0, 0);
        }

        self.get_hash(range.start, range.end)
    }

    #[inline]
    /// return the hash of s[l..r)
    fn get_hash(&self, l: usize, r: usize) -> HashValue {
        let cache = POW_CACHE.lock().unwrap();
        let (res, f) = self.hash[r].overflowing_sub(mul(self.hash[l], cache[r - l]));
        HashValue::new(r - l, res.wrapping_add(MOD & (f as u64).wrapping_neg()))
    }

    /// Return the length of Longest Common Prefix between `self` and `other`.
    ///
    /// # Example
    /// ```rust
    /// use string::RollingHash;
    ///
    /// let s = RollingHash::new("abcdefg");
    /// let t = RollingHash::new("abcdfg");
    ///
    /// // "abcdefg" and "abcdfg"
    /// assert_eq!(s.lcp(.., &t, ..), 4);
    /// // "bcdefg" and "bcdfg"
    /// assert_eq!(s.lcp(1.., &t, 1..), 3);
    /// // "abcdefg" and "bcdfg"
    /// assert_eq!(s.lcp(.., &t, 1..), 0);
    /// // "fg" and "fg"
    /// assert_eq!(s.lcp(5.., &t, 4..), 2);
    /// ```
    pub fn lcp(
        &self,
        range: impl RangeBounds<usize>,
        other: &Self,
        range_other: impl RangeBounds<usize>,
    ) -> usize {
        let range = self.convert_range(range);
        let range_other = other.convert_range(range_other);

        if range.is_empty() || range_other.is_empty() {
            return 0;
        }

        let len = range.len().min(range_other.len());
        let start = range.start;
        let start_other = range_other.start;
        let (mut l, mut r) = (0, len + 1);
        while r - l > 1 {
            let m = (r + l) / 2;
            if self.get(start..start + m) == other.get(start_other..start_other + m) {
                l = m;
            } else {
                r = m;
            }
        }
        l
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct HashValue {
    len: usize,
    hash: u64,
}

impl HashValue {
    fn new(len: usize, hash: u64) -> Self { Self { len, hash } }

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
}

impl Add for HashValue {
    type Output = HashValue;
    fn add(self, rhs: Self) -> Self::Output { self.concat(rhs) }
}
