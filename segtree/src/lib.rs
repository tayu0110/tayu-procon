mod lazy_segtree;

pub use lazy_segtree::*;

#[derive(Debug, Clone)]
pub struct SegmentTree<M: Clone> {
    size: usize,
    e: M,
    op: fn(&M, &M) -> M,
    tree: Vec<M>,
}

impl<M: Clone> SegmentTree<M> {
    /// * `size` - Number of elements in the data array to be managed
    /// * `e`    - Identity element of the monoid that the data represents
    /// * `op`   - Operation applied to data (If the operation is to fold the data toward the right, op(a, b) must return b*a as the result)
    #[inline]
    pub fn new(size: usize, e: M, op: fn(&M, &M) -> M) -> Self {
        let tree = vec![e.clone(); size << 1];
        Self { size, e, op, tree }
    }

    /// * `vec`  - Initial state of the data array to be managed
    /// * `e`    - Identity element of the monoid that the data represents
    /// * `op`   - Operation applied to data (If the operation is to fold the data toward the right, op(a, b) must return b*a as the result)
    pub fn from_vec(vec: &Vec<M>, e: M, op: fn(&M, &M) -> M) -> Self {
        let size = vec.len();
        let mut tree = [vec![e.clone(); size], vec.clone()].concat();

        for i in (0..(size << 1) - 1)
            .rev()
            .step_by(2)
            .take_while(|i| i >> 1 > 0 as usize)
        {
            tree[i >> 1] = op(&tree[i], &tree[i | 1]);
        }

        Self { size, e, op, tree }
    }

    #[inline]
    pub fn set(&mut self, index: usize, val: M) {
        self.update_by(index, val, |_, act| act.clone());
    }

    pub fn update_by(&mut self, mut index: usize, val: M, f: fn(old: &M, act: &M) -> M) {
        index += self.size;
        self.tree[index] = f(&self.tree[index], &val);
        while index >> 1 > 0 {
            index >>= 1;
            self.tree[index] = self.op(&self.tree[index << 1], &self.tree[index << 1 | 1], false);
        }
    }

    fn fold(&self, left: usize, right: usize, fold_right: bool) -> M {
        if left >= right {
            return self.e.clone();
        }

        let (mut l, mut r) = (left + self.size, right + self.size);
        let (mut res_l, mut res_r) = (self.e.clone(), self.e.clone());
        while l < r {
            if l & 1 != 0 {
                res_l = self.op(&self.tree[l], &res_l, fold_right);
                l += 1;
            }
            if r & 1 != 0 {
                res_r = self.op(&res_r, &self.tree[r - 1], fold_right);
            }
            l >>= 1;
            r >>= 1;
        }

        self.op(&res_l, &res_r, false)
    }

    /// Fold the operation in a leftward direction.
    /// That is, you obtain op(t_{l}, op(t_{l+1}, op(t_{l+2}, ...op(t_{r-2}, t_{r-1})...))) as a result.
    #[inline]
    pub fn foldl(&self, left: usize, right: usize) -> M { self.fold(left, right, false) }

    /// Fold the operation in a rightward direction.
    /// That is, you obtain op(op(op(...op(t_{l}, t_{l+1}), t_{l+2}), ..., t_{r-2}), t_{r_1}) as a result.
    #[inline]
    pub fn foldr(&self, left: usize, right: usize) -> M { self.fold(left, right, true) }

    #[inline]
    fn op(&self, lhs: &M, rhs: &M, fold_right: bool) -> M {
        if !fold_right {
            (self.op)(&lhs, &rhs)
        } else {
            (self.op)(&rhs, &lhs)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{
        RangeAddRangeMaximumQuery, RangeAddRangeMinimumQuery, RangeAddRangeSumQuery, SegmentTree,
    };

    #[test]
    fn segtree_test() {
        let v = [1, 3, 4, 7, 14, 3, 6, 4, 11, 9];

        let mut st = SegmentTree::from_vec(&v.to_vec(), 0, |l, r| *l + *r);
        // The above code is same meaning as the following code.
        //
        // let mut st = SegmentTree::new(10, 0, |l, r| *l + *r);
        // for (i, w) in v.into_iter().enumerate() {
        //     st.set(i, w);
        // }

        assert_eq!(st.foldl(0, 10), 62);
        assert_eq!(st.foldl(5, 10), 33);
        assert_eq!(st.foldl(0, 5), 29);
        assert_eq!(st.foldl(3, 7), 30);

        st.set(4, -1);

        assert_eq!(st.foldl(0, 10), 47);
        assert_eq!(st.foldl(5, 10), 33);
        assert_eq!(st.foldl(0, 5), 14);
        assert_eq!(st.foldl(3, 7), 15);

        st.update_by(4, 15, |old, val| old + val);

        assert_eq!(st.foldl(0, 10), 62);
        assert_eq!(st.foldl(5, 10), 33);
        assert_eq!(st.foldl(0, 5), 29);
        assert_eq!(st.foldl(3, 7), 30);

        st.update_by(6, 3, |old, val| old * val);

        assert_eq!(st.foldl(0, 10), 74);
        assert_eq!(st.foldl(5, 10), 45);
        assert_eq!(st.foldl(0, 5), 29);
        assert_eq!(st.foldl(3, 7), 42);
    }

    #[test]
    fn lazy_segtree_test() {
        let v = [1, 3, 4, 7, 14, 3, 6, 4, 11, 9];

        let mut st = RangeAddRangeMaximumQuery::new(10);
        // let mut st = range_add_range_maximum_query(10);
        for (i, w) in v.iter().enumerate() {
            st.apply(i, *w);
        }

        assert_eq!(st.prod(0, 10), 14);
        assert_eq!(st.prod(5, 10), 11);
        assert_eq!(st.prod(0, 5), 14);
        assert_eq!(st.prod(5, 8), 6);

        // let mut st = range_add_range_minimum_query(10);
        let mut st = RangeAddRangeMinimumQuery::new(10);
        for (i, w) in v.iter().enumerate() {
            st.apply(i, *w);
        }

        assert_eq!(st.prod(0, 10), 1);
        assert_eq!(st.prod(5, 10), 3);
        assert_eq!(st.prod(0, 5), 1);
        assert_eq!(st.prod(2, 5), 4);

        // let mut st = range_add_range_sum_query(10);
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
