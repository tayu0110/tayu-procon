use std::{
    collections::{btree_map, BTreeMap},
    fmt::Debug,
    iter::FusedIterator,
    ops::RangeBounds,
};

pub struct BTreeMultiSet<K> {
    len: usize,
    inner: BTreeMap<K, u32>,
}

impl<'a, K: Ord + Debug + Clone> BTreeMultiSet<K> {
    #[inline]
    pub fn new() -> Self { Self { len: 0, inner: BTreeMap::new() } }
    #[inline]
    pub fn insert(&mut self, key: K) {
        *self.inner.entry(key).or_insert(0) += 1;
        self.len += 1;
    }
    #[inline]
    pub fn remove(&mut self, key: &K) {
        if !self.inner.contains_key(key) {
            return;
        }

        self.len -= 1;
        if *self.inner.get(key).unwrap() == 1 {
            self.inner.remove(key);
        } else {
            *self.inner.get_mut(key).unwrap() -= 1;
        }
    }
    #[inline]
    pub fn remove_all(&mut self, key: &K) {
        self.len -= *self.inner.get(key).unwrap_or(&0) as usize;
        self.inner.remove(key);
    }
    #[inline]
    pub fn count(&mut self, key: &K) -> usize { *self.inner.get(key).unwrap_or(&0) as usize }
    #[inline]
    pub fn len(&self) -> usize { self.len }
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
        self.len = 0;
    }
    #[inline]
    pub fn has_duplicate(&self) -> bool { self.len() != self.inner.len() }
    #[inline]
    pub fn contains(&self, key: &K) -> bool { self.inner.contains_key(key) }
    #[inline]
    pub fn first(&self) -> Option<&K> { self.inner.iter().next().map(|(k, _)| k) }
    #[inline]
    pub fn get(&self, key: &K) -> Option<&K> { self.inner.get_key_value(key).map(|(k, _)| k) }
    #[inline]
    pub fn is_empty(&self) -> bool { self.inner.is_empty() }
    #[inline]
    pub fn last(&self) -> Option<&K> { self.inner.iter().rev().next().map(|(k, _)| k) }
    #[inline]
    pub fn iter(&'a self) -> Iter<'a, K, btree_map::Iter<'a, K, u32>> {
        Iter::new(self.inner.iter())
    }
    #[inline]
    pub fn range<R: RangeBounds<K>>(
        &'a self,
        range: R,
    ) -> Iter<'a, K, btree_map::Range<'a, K, u32>> {
        Iter::new(self.inner.range(range))
    }
}

impl<K: Ord + Debug + Clone> Default for BTreeMultiSet<K> {
    fn default() -> Self { Self::new() }
}

#[derive(Debug)]
pub struct Iter<'a, K, I>
where
    K: Ord,
    I: Iterator<Item = (&'a K, &'a u32)>
        + DoubleEndedIterator<Item = (&'a K, &'a u32)>
        + FusedIterator
        + Debug
        + Clone,
{
    fvalue: Option<&'a K>,
    frem: u32,
    bvalue: Option<&'a K>,
    brem: u32,
    iter: I,
}

impl<'a, K, I> Iter<'a, K, I>
where
    K: Ord,
    I: Iterator<Item = (&'a K, &'a u32)>
        + DoubleEndedIterator<Item = (&'a K, &'a u32)>
        + FusedIterator
        + Debug
        + Clone,
{
    fn new(iter: I) -> Self { Self { fvalue: None, frem: 0, bvalue: None, brem: 0, iter } }
}

impl<'a, K, I> Iterator for Iter<'a, K, I>
where
    K: Ord,
    I: Iterator<Item = (&'a K, &'a u32)>
        + DoubleEndedIterator<Item = (&'a K, &'a u32)>
        + FusedIterator
        + Debug
        + Clone,
{
    type Item = &'a K;
    fn next(&mut self) -> Option<Self::Item> {
        if self.frem == 0 {
            if let Some((k, v)) = self.iter.next() {
                self.fvalue = Some(k);
                self.frem = *v;
            } else if self.brem > 0 {
                self.brem -= 1;
                return self.bvalue;
            } else {
                return None;
            }
        }

        self.frem -= 1;
        self.fvalue
    }
}

impl<'a, K, I> DoubleEndedIterator for Iter<'a, K, I>
where
    K: Ord,
    I: Iterator<Item = (&'a K, &'a u32)>
        + DoubleEndedIterator<Item = (&'a K, &'a u32)>
        + FusedIterator
        + Debug
        + Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.brem == 0 {
            if let Some((k, v)) = self.iter.next_back() {
                self.bvalue = Some(k);
                self.brem = *v;
            } else if self.frem > 0 {
                self.frem -= 1;
                return self.fvalue;
            } else {
                return None;
            }
        }

        self.brem -= 1;
        self.bvalue
    }
}

impl<'a, K, I> FusedIterator for Iter<'a, K, I>
where
    K: Ord,
    I: Iterator<Item = (&'a K, &'a u32)>
        + DoubleEndedIterator<Item = (&'a K, &'a u32)>
        + FusedIterator
        + Debug
        + Clone,
{
}
