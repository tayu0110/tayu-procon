#![allow(clippy::uninit_assumed_init)]

use std::mem::MaybeUninit;

pub struct FixedRingQueue<T, const SIZE: usize = { 1 << 20 }> {
    buf: [MaybeUninit<T>; SIZE],
    head: usize,
    tail: usize,
}

impl<T, const SIZE: usize> FixedRingQueue<T, SIZE> {
    const MASK: usize = {
        assert!(1 << SIZE.trailing_zeros() == SIZE);
        SIZE - 1
    };

    pub const fn new() -> Self {
        Self {
            buf: unsafe { MaybeUninit::uninit().assume_init() },
            head: 0,
            tail: 0,
        }
    }

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
            let res = std::mem::replace(
                &mut self.buf[(self.head) & Self::MASK],
                MaybeUninit::uninit(),
            );
            self.head += 1;
            unsafe { res.assume_init() }
        })
    }
}

impl<T, const SIZE: usize> FromIterator<T> for FixedRingQueue<T, SIZE> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut que = FixedRingQueue::new();
        iter.into_iter().for_each(|v| que.push(v));
        que
    }
}

impl<T, const SIZE: usize> Extend<T> for FixedRingQueue<T, SIZE> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        iter.into_iter().for_each(|v| self.push(v));
    }
}
