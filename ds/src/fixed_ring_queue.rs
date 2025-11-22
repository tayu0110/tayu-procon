#![allow(clippy::uninit_assumed_init)]

use std::mem::MaybeUninit;

pub struct FixedRingQueue<T, const SIZE: usize = { 1 << 20 }> {
    buf: [MaybeUninit<T>; SIZE],
    head: usize,
    tail: usize,
    empty: bool,
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
            empty: true,
        }
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.empty
    }

    #[inline]
    pub fn is_full(&self) -> bool {
        self.len() == SIZE
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.tail - self.head
    }

    #[inline]
    pub fn capacity(&self) -> usize {
        SIZE
    }

    #[inline]
    pub fn clear(&mut self) {
        self.head = 0;
        self.tail = 0;
        self.empty = true;
    }

    pub fn push(&mut self, val: T) {
        debug_assert!(!self.is_full());
        unsafe {
            self.buf
                .as_mut_ptr()
                .add(self.tail & Self::MASK)
                .as_mut()
                .unwrap_unchecked()
                .write(val)
        };
        self.tail += 1;
        self.empty = false;
    }

    /// # Safety
    /// * This method does not verify that the queue is empty.
    /// * You can only use this method if it was verified beforehand using `is_empty()` (which is the same as using `pop()`), or if the routine is certain that the queue will never be empty.
    #[inline]
    pub unsafe fn pop_unchecked(&mut self) -> T {
        let res = unsafe {
            std::ptr::replace(
                self.buf.as_mut_ptr().add(self.head & Self::MASK),
                MaybeUninit::uninit(),
            )
        };
        self.head += 1;
        self.empty = self.head == self.tail;
        res.assume_init()
    }

    #[inline]
    pub fn pop(&mut self) -> Option<T> {
        (!self.is_empty()).then(|| unsafe { self.pop_unchecked() })
    }
}

impl<T, const SIZE: usize> Default for FixedRingQueue<T, SIZE> {
    fn default() -> Self {
        Self::new()
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
