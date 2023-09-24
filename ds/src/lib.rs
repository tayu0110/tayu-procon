use std::{
    collections::{btree_map, BTreeMap},
    fmt::Debug,
    iter::FusedIterator,
    mem::MaybeUninit,
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
    pub fn iter(&'a self) -> Iter<'a, K, btree_map::Iter<'a, K, u32>> { Iter::new(self.inner.iter()) }
    #[inline]
    pub fn range<R: RangeBounds<K>>(&'a self, range: R) -> Iter<'a, K, btree_map::Range<'a, K, u32>> { Iter::new(self.inner.range(range)) }
}

#[derive(Debug)]
pub struct Iter<'a, K, I>
where
    K: Ord,
    I: Iterator<Item = (&'a K, &'a u32)> + DoubleEndedIterator<Item = (&'a K, &'a u32)> + FusedIterator + Debug + Clone,
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
    I: Iterator<Item = (&'a K, &'a u32)> + DoubleEndedIterator<Item = (&'a K, &'a u32)> + FusedIterator + Debug + Clone,
{
    fn new(iter: I) -> Self { Self { fvalue: None, frem: 0, bvalue: None, brem: 0, iter } }
}

impl<'a, K, I> Iterator for Iter<'a, K, I>
where
    K: Ord,
    I: Iterator<Item = (&'a K, &'a u32)> + DoubleEndedIterator<Item = (&'a K, &'a u32)> + FusedIterator + Debug + Clone,
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
    I: Iterator<Item = (&'a K, &'a u32)> + DoubleEndedIterator<Item = (&'a K, &'a u32)> + FusedIterator + Debug + Clone,
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
    I: Iterator<Item = (&'a K, &'a u32)> + DoubleEndedIterator<Item = (&'a K, &'a u32)> + FusedIterator + Debug + Clone,
{
}

pub struct FixedRingQueue<T, const SIZE: usize = { 1 << 20 }> {
    buf: [MaybeUninit<T>; SIZE],
    head: usize,
    tail: usize,
}

impl<T: Clone + Copy, const SIZE: usize> FixedRingQueue<T, SIZE> {
    const MASK: usize = {
        assert!(1 << SIZE.trailing_zeros() == SIZE);
        SIZE - 1
    };

    pub const fn new() -> Self { Self { buf: [MaybeUninit::uninit(); SIZE], head: 0, tail: 0 } }

    #[inline]
    pub fn is_empty(&self) -> bool { self.head == self.tail }

    #[inline]
    pub fn is_full(&self) -> bool { self.len() == SIZE }

    #[inline]
    pub fn len(&self) -> usize { self.tail - self.head }

    #[inline]
    pub fn capacity(&self) -> usize { SIZE }

    #[inline]
    pub fn clear(&mut self) {
        self.head = 0;
        self.tail = 0;
    }

    pub fn push(&mut self, val: T) {
        debug_assert!(!self.is_full());
        self.buf[self.tail & Self::MASK].write(val);
        self.tail += 1;
    }

    pub fn pop(&mut self) -> Option<T> {
        (!self.is_empty()).then(|| {
            let res = unsafe { self.buf[(self.head) & Self::MASK].assume_init() };
            self.head += 1;
            res
        })
    }
}

impl<T: Clone + Copy, const SIZE: usize> FromIterator<T> for FixedRingQueue<T, SIZE> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut que = FixedRingQueue::new();
        iter.into_iter().for_each(|v| que.push(v));
        que
    }
}

impl<T: Clone + Copy, const SIZE: usize> Extend<T> for FixedRingQueue<T, SIZE> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) { iter.into_iter().for_each(|v| self.push(v)); }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multiset_test() {
        let mut multiset = BTreeMultiSet::new();
        multiset.insert(0u32);
        assert_eq!(multiset.count(&0), 1);

        multiset.insert(0);
        multiset.insert(0);
        assert_eq!(multiset.count(&0), 3);

        multiset.remove(&0);
        assert_eq!(multiset.count(&0), 2);
        assert!(multiset.has_duplicate());

        multiset.insert(10);
        multiset.insert(2);
        multiset.insert(1);

        assert_eq!(multiset.len(), 5);
        assert_eq!(multiset.last().unwrap(), &10);
        assert!(multiset.contains(&2));
        assert!(!multiset.contains(&3));

        let mut iter = multiset.iter();
        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&10));
        assert_eq!(iter.next(), None);

        let mut range = multiset.range(1..);
        assert_eq!(range.next(), Some(&1));
        assert_eq!(range.next(), Some(&2));
        assert_eq!(range.next(), Some(&10));
        assert_eq!(range.next(), None);

        multiset.remove_all(&0);
        assert!(!multiset.contains(&0));
        assert_eq!(multiset.len(), 3);
        assert!(!multiset.has_duplicate());
    }

    #[test]
    fn ring_queue_test() {
        const SIZE: usize = 1 << 5;
        let mut nt = FixedRingQueue::<i32, SIZE>::new();

        assert!(nt.is_empty());

        nt.push(1);
        nt.push(2);
        nt.push(10);
        nt.push(5);

        assert_eq!(nt.len(), 4);
        assert!(!nt.is_full());
        assert_eq!(nt.pop().expect("why queue is empty?"), 1);

        for i in 0..(1 << 5) - 3 {
            nt.push(i);
        }

        assert!(nt.is_full());

        assert_eq!(nt.pop().expect("why queue is empty"), 2);
        assert_eq!(nt.pop().expect("why queue is empty"), 10);
        assert_eq!(nt.pop().expect("why queue is empty"), 5);
        assert_eq!(nt.pop().expect("why queue is empty"), 0);

        while let Some(_) = nt.pop() {}

        assert!(nt.is_empty());
    }
}
