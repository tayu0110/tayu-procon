use super::{mul, HashValue, MOD, POW_CACHE};
use std::ops::{Bound, Range, RangeBounds};

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
