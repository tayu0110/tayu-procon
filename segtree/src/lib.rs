mod lazy_segtree;

pub use lazy_segtree::*;
use std::ops::{Bound, Range, RangeBounds};

fn convert_range(min: usize, max: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    let l = match range.start_bound() {
        Bound::Included(l) => *l,
        Bound::Unbounded => min,
        Bound::Excluded(l) => l - 1,
    };
    let r = match range.end_bound() {
        Bound::Included(r) => r + 1,
        Bound::Excluded(r) => *r,
        Bound::Unbounded => max,
    };
    Range { start: l, end: r }
}

pub trait Monoid {
    type M;
    fn id() -> Self::M;
    fn op(l: &Self::M, r: &Self::M) -> Self::M;
}

pub struct SegmentTree<T: Monoid> {
    t: Vec<T::M>,
}

impl<T: Monoid> SegmentTree<T> {
    pub fn new(size: usize) -> Self {
        Self { t: (0..size * 2).map(|_| T::id()).collect() }
    }

    pub fn from_vec(v: Vec<T::M>) -> Self {
        let size = v.len();
        let mut t = (0..size).map(|_| T::id()).chain(v).collect::<Vec<_>>();

        for i in (1..size).rev() {
            t[i] = T::op(&t[i << 1], &t[(i << 1) | 1]);
        }

        Self { t }
    }

    pub fn len(&self) -> usize {
        self.t.len() >> 1
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn set(&mut self, mut index: usize, val: T::M) {
        assert!(index < self.len());

        index += self.len();
        self.t[index] = val;
        while index > 1 {
            let (l, r) = (index.min(index ^ 1), index.max(index ^ 1));
            self.t[index >> 1] = T::op(&self.t[l], &self.t[r]);
            index >>= 1;
        }
    }

    pub fn update_by<F>(&mut self, index: usize, f: F)
    where
        F: Fn(&T::M) -> T::M,
    {
        assert!(index < self.len());
        let new = f(&self.t[index + self.len()]);
        self.set(index, new);
    }

    pub fn fold(&self, range: impl RangeBounds<usize>) -> T::M {
        let Range { start, end } = convert_range(0, self.len(), range);

        let (mut l, mut r) = (start + self.len(), end + self.len());
        let (mut lf, mut rf) = (T::id(), T::id());
        while l < r {
            if l & 1 != 0 {
                lf = T::op(&lf, &self.t[l]);
                l += 1;
            }
            if r & 1 != 0 {
                rf = T::op(&self.t[r - 1], &rf);
            }
            l >>= 1;
            r >>= 1;
        }

        T::op(&lf, &rf)
    }
}

#[derive(Debug, Clone)]
pub struct Reversible<T: Monoid + Clone> {
    pub forward: T,
    pub reverse: T,
}

impl<T: Monoid + Clone> Reversible<T> {
    pub fn new(val: T) -> Self {
        Self { forward: val.clone(), reverse: val }
    }
}

impl<T: Monoid<M = T> + Clone> Monoid for Reversible<T> {
    type M = Self;
    fn id() -> Self::M {
        Self { forward: T::id(), reverse: T::id() }
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        Self {
            forward: T::op(&l.forward, &r.forward),
            reverse: T::op(&r.reverse, &l.reverse),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::Monoid;

    use super::{
        RangeAddRangeMaximumQuery, RangeAddRangeMinimumQuery, RangeAddRangeSumQuery, SegmentTree,
    };

    #[test]
    fn segtree_test() {
        let v = [1, 3, 4, 7, 14, 3, 6, 4, 11, 9];

        struct I32Add;
        impl Monoid for I32Add {
            type M = i32;
            fn id() -> Self::M {
                0
            }
            fn op(l: &Self::M, r: &Self::M) -> Self::M {
                l + r
            }
        }

        let mut st = SegmentTree::<I32Add>::from_vec(v.to_vec());

        assert_eq!(st.fold(0..10), 62);
        assert_eq!(st.fold(5..10), 33);
        assert_eq!(st.fold(0..5), 29);
        assert_eq!(st.fold(3..7), 30);

        st.set(4, -1);

        assert_eq!(st.fold(0..10), 47);
        assert_eq!(st.fold(5..10), 33);
        assert_eq!(st.fold(0..5), 14);
        assert_eq!(st.fold(3..7), 15);

        st.update_by(4, |old| old + 15);

        assert_eq!(st.fold(0..10), 62);
        assert_eq!(st.fold(5..10), 33);
        assert_eq!(st.fold(0..5), 29);
        assert_eq!(st.fold(3..7), 30);

        st.update_by(6, |old| old * 3);

        assert_eq!(st.fold(0..10), 74);
        assert_eq!(st.fold(5..10), 45);
        assert_eq!(st.fold(0..5), 29);
        assert_eq!(st.fold(3..7), 42);
    }

    #[test]
    fn lazy_segtree_test() {
        let v = [1, 3, 4, 7, 14, 3, 6, 4, 11, 9];

        let mut st = RangeAddRangeMaximumQuery::new(10);
        for (i, w) in v.iter().enumerate() {
            st.apply(i, *w);
        }

        assert_eq!(st.prod(0, 10), 14);
        assert_eq!(st.prod(5, 10), 11);
        assert_eq!(st.prod(0, 5), 14);
        assert_eq!(st.prod(5, 8), 6);

        let mut st = RangeAddRangeMinimumQuery::new(10);
        for (i, w) in v.iter().enumerate() {
            st.apply(i, *w);
        }

        assert_eq!(st.prod(0, 10), 1);
        assert_eq!(st.prod(5, 10), 3);
        assert_eq!(st.prod(0, 5), 1);
        assert_eq!(st.prod(2, 5), 4);

        let mut st = RangeAddRangeSumQuery::new(10);
        for (i, w) in v.iter().enumerate() {
            st.apply(i, *w);
        }

        assert_eq!(st.prod(0, 10).0, 62);
        assert_eq!(st.prod(5, 10).0, 33);
        assert_eq!(st.prod(0, 5).0, 29);
        assert_eq!(st.prod(3, 7).0, 30);
    }
}
