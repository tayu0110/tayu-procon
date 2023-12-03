use super::{mul, HashValue, MOD, POW_CACHE};
use segtree::SegmentTree;
use std::ops::{Bound, Range, RangeBounds};

pub struct DynamicRollingHash {
    len: usize,
    hash: SegmentTree<(u64, u64)>,
}

impl DynamicRollingHash {
    /// Generate the rolling hash for a string `s`.
    #[inline]
    pub fn new(s: &str) -> Self {
        {
            let mut cache = POW_CACHE.lock().unwrap();
            cache.grow(s.len());
        }

        let hash = SegmentTree::from_vec(
            &s.chars().map(|c| (c as u64, 1u64)).collect(),
            (0, 0),
            |l, r| {
                if r.1 == 0 {
                    return *l;
                } else if l.1 == 0 {
                    return *r;
                }
                let base = POW_CACHE.lock().unwrap().base();
                let b = mul(r.1, base);
                let mut val = mul(l.0, b) + r.0;
                if val >= MOD {
                    val -= MOD;
                }
                (val, mul(b, l.1))
            },
        );

        Self { len: s.len(), hash }
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
            Bound::Unbounded => self.len,
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

    /// return the hash of s[l..r)
    #[inline]
    fn get_hash(&self, l: usize, r: usize) -> HashValue {
        let (res, _) = self.hash.foldr(l, r);
        HashValue::new(r - l, res)
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

    /// Change n-th character of the string managed `self` to `val`
    #[inline]
    pub fn set(&mut self, index: usize, val: char) {
        self.hash.set(index, (val as u64, 1));
    }
}
