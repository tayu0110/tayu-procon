use super::{HashValue, SplayTree, POW_CACHE};
use std::ops::{Bound, Range, RangeBounds};

pub struct DynamicRollingHash {
    hash: SplayTree,
}

impl DynamicRollingHash {
    /// Generate the rolling hash for a string `s`.
    #[inline]
    pub fn new(s: &str) -> Self {
        {
            let mut cache = POW_CACHE.lock().unwrap();
            cache.grow(s.len());
        }

        // let mut hash = SplayTree::new();
        // for (i, c) in s.chars().enumerate() {
        //     hash.insert(i, c).unwrap();
        // }

        Self { hash: s.chars().collect() }
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
            Bound::Unbounded => self.hash.len(),
        };
        Range { start: l, end: r }
    }

    /// Get the hash value of substring of `s` that you use generating RollingHash::new().
    ///
    /// # Example
    /// ```rust
    /// use string::DynamicRollingHash;
    ///
    /// let s = "abdabfgdabfgda";
    /// let mut hash = DynamicRollingHash::new(s);
    ///
    /// // you can use RangeTo, Range,
    /// assert_eq!(hash.get(..2), hash.get(3..5));
    /// // RangeInclusive, RangeFrom,
    /// assert_eq!(hash.get(3..=8), hash.get(8..));
    /// // RangeFull, and so on
    /// assert_ne!(hash.get(..), hash.get(..=5));
    /// ```
    #[inline]
    pub fn get(&mut self, range: impl RangeBounds<usize>) -> HashValue {
        let range = self.convert_range(range);

        if range.is_empty() {
            return HashValue::new(0, 0);
        }

        self.get_hash(range.start, range.end)
    }

    /// return the hash of s[l..r)
    #[inline]
    fn get_hash(&mut self, l: usize, r: usize) -> HashValue {
        let res = self.hash.fold(l..r).unwrap();
        HashValue::new(r - l, res)
    }

    #[inline]
    pub fn get_reverse(&mut self, range: impl RangeBounds<usize>) -> HashValue {
        let range = self.convert_range(range);

        if range.is_empty() {
            return HashValue::new(0, 0);
        }

        self.get_hash_reverse(range.start, range.end)
    }

    fn get_hash_reverse(&mut self, l: usize, r: usize) -> HashValue {
        let res = self.hash.fold_reverse(l..r).unwrap();
        HashValue::new(r - l, res)
    }

    pub fn is_palindrome(&mut self, range: impl RangeBounds<usize>) -> bool {
        let range = self.convert_range(range);

        if range.is_empty() {
            return true;
        }

        let (f, r) = self.hash.fold_both(range).unwrap();
        f == r
    }

    /// Return the length of Longest Common Prefix between `self` and `other`.
    ///
    /// # Example
    /// ```rust
    /// use string::DynamicRollingHash;
    ///
    /// let mut s = DynamicRollingHash::new("abcdefg");
    /// let mut t = DynamicRollingHash::new("abcdfg");
    ///
    /// // "abcdefg" and "abcdfg"
    /// assert_eq!(s.lcp(.., &mut t, ..), 4);
    /// // "bcdefg" and "bcdfg"
    /// assert_eq!(s.lcp(1.., &mut t, 1..), 3);
    /// // "abcdefg" and "bcdfg"
    /// assert_eq!(s.lcp(.., &mut t, 1..), 0);
    /// // "fg" and "fg"
    /// assert_eq!(s.lcp(5.., &mut t, 4..), 2);
    /// ```
    pub fn lcp(
        &mut self,
        range: impl RangeBounds<usize>,
        other: &mut Self,
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
        self.hash.set(index, val).unwrap();
    }

    pub fn reverse(&mut self, range: impl RangeBounds<usize>) {
        let range = self.convert_range(range);
        self.hash.reverse(range).unwrap();
    }

    /// this is still not vefified...
    pub fn insert(&mut self, index: usize, val: char) {
        self.hash.insert(index, val).unwrap();
    }

    /// this is still not vefified...
    pub fn remove(&mut self, index: usize) {
        self.hash.remove(index).unwrap();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::RollingHash;
    use rand::{
        distributions::{Alphanumeric, DistString},
        thread_rng, Rng,
    };

    #[test]
    fn updatable_rolling_hash_test() {
        let mut hash = DynamicRollingHash::new("abcdefghij");

        assert_eq!(hash.get(..), RollingHash::new("abcdefghij").get(..));
        assert_eq!(hash.get(..5), RollingHash::new("abcdefghij").get(..5));
        assert_eq!(hash.get(5..), RollingHash::new("abcdefghij").get(5..));
        assert_eq!(hash.get(3..6), RollingHash::new("abcdefghij").get(3..6));

        hash.set(0, 'z');
        assert_eq!(hash.get(..), RollingHash::new("zbcdefghij").get(..));
        hash.set(3, 'w');
        assert_eq!(hash.get(..), RollingHash::new("zbcwefghij").get(..));

        hash.reverse(..);
        assert_eq!(hash.get(..), RollingHash::new("jihgfewcbz").get(..));
        hash.reverse(1..5);
        assert_eq!(hash.get(..), RollingHash::new("jfghiewcbz").get(..));
        hash.reverse(3..8);
        assert_eq!(hash.get(..), RollingHash::new("jfgcweihbz").get(..));
    }

    #[test]
    fn updatable_rolling_hash_random_test() {
        let mut rng = thread_rng();
        const LEN: usize = 10;

        for _ in 0..100 {
            let s = Alphanumeric.sample_string(&mut rng, LEN);

            let mut hash = DynamicRollingHash::new(&s);

            let start = rng.gen_range(0..LEN);
            let end = rng.gen_range(start..LEN + 1);
            eprint!("s: {s}, start: {start}, end: {end} ");
            hash.reverse(start..end);

            let mut s = s.chars().collect::<Vec<char>>();
            s[start..end].reverse();
            let s = s.into_iter().collect::<String>();
            eprintln!("revs: {s}");
            let verify = RollingHash::new(&s);

            assert_eq!(hash.get(..), verify.get(..));
        }
    }
}
