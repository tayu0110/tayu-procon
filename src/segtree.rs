pub struct SegmentTree<M>
where M: Clone {
    size: usize,
    e: M,
    op: fn(&M, &M) -> M,
    tree: Vec<M>
}

impl<M> SegmentTree<M>
where M: Clone {
    #[inline]
    pub fn new(size: usize, e: M, op: fn(&M, &M) -> M) -> Self {
        let tree = vec![e.clone(); size << 1];
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
            self.tree[index] = self.op(&self.tree[index<<1], &self.tree[index<<1|1]);
        }
    }
    
    pub fn get(&self, left: usize, right: usize) -> M {
        if left >= right {
            return self.e.clone();
        }

        let (mut l, mut r) = (left + self.size, right + self.size);
        let (mut res_l, mut res_r) = (self.e.clone(), self.e.clone());
        while l < r {
            if l & 1 != 0 {
                res_l = self.op(&self.tree[l], &res_l);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                res_r = self.op(&res_r, &self.tree[r]);
            }
            l >>= 1;
            r >>= 1;
        }

        self.op(&res_l, &res_r)
    }

    #[inline]
    fn op(&self, lhs: &M, rhs: &M) -> M { let op = self.op; op(&lhs, &rhs) }
}

pub struct LazySegtree<S, F> {
    n: usize,
    size: usize,
    log: usize,
    pub tree: Vec<S>,
    pub lazy: Vec<F>,
    op: fn(S, S) -> S,
    e: fn() -> S,
    id: fn() -> F,
    mapping: fn(F, S) -> S,
    composition: fn(F, F) -> F
}

impl<S, F> LazySegtree<S, F>
where
    S: Copy + Clone + Sized,
    F: Copy + Clone + Sized
{
    pub fn new(
            size: usize,
            op: fn(S, S) -> S,
            e: fn() -> S,
            id: fn() -> F,
            mapping: fn(F, S) -> S,
            composition: fn(F, F) -> F) -> Self {
        LazySegtree::from_vec(&vec![e(); size], op, e, id, mapping, composition)
    }

    pub fn from_vec(
            v: &Vec<S>,
            op: fn(S, S) -> S,
            e: fn() -> S,
            id: fn() -> F,
            mapping: fn(F, S) -> S,
            composition: fn(F, F) -> F) -> Self {
        let n = v.len();
        let size = n.next_power_of_two();
        let log = size.trailing_zeros() as usize;
        let mut tree = vec![e(); size * 2];
        let lazy = vec![id(); size * 2];
        tree.iter_mut().skip(size).zip(v.iter()).for_each(|(t, w)| *t = *w);
        for i in (1..size).rev() {
            tree[i] = op(tree[i*2], tree[i*2 + 1]);
        }
        Self { n, size, log, tree, lazy, op, e, id, mapping, composition }
    }
    pub fn set(&mut self, idx: usize, val: S) {
        assert!(idx < self.n);
        let idx = idx + self.size;
        for i in (1..self.log+1).rev() {
            self.push(idx >> i);
        }
        self.tree[idx] = val;
        for i in 1..=self.log {
            self.update(idx >> i);
        }
    }
    // Get the value of a single point whose index is idx.
    pub fn get(&mut self, idx: usize) -> S {
        assert!(idx < self.n);
        let idx = idx + self.size;
        for i in (1..self.log+1).rev() {
            self.push(idx >> i);
        }
        self.tree[idx]
    }
    // Get the result of applying the operation to the interval [l, r).
    pub fn prod(&mut self, l: usize, r: usize) -> S {
        assert!(l <= r && r <= self.n);
        if l == r {
            return self.e();
        }
        let (mut l, mut r) = (l + self.size, r + self.size);
        for i in (1..self.log+1).rev() {
            if ((l >> i) << i) != l {
                self.push(l >> i);
            }
            if ((r >> i) << i) != r {
                self.push(r >> i);
            }
        }
        let (mut sml, mut smr) = (self.e(), self.e());
        while l < r {
            if (l & 1) != 0 {
                sml = self.op(sml, self.tree[l]);
                l += 1;
            }
            if (r & 1) != 0 {
                r -= 1;
                smr = self.op(self.tree[r], smr);
            }
            l >>= 1; r >>= 1;
        }
        self.op(sml, smr)
    }
    pub fn all_prod(&self) -> S {
        self.tree[1]
    }
    // Apply val to a point whose index is idx.
    pub fn apply(&mut self, idx: usize, val: F) {
        assert!(idx < self.n);
        let idx = idx + self.size;
        for i in (1..self.log+1).rev() {
            self.push(idx >> i);
        }
        self.tree[idx] = self.mapping(val, self.tree[idx]);
        for i in 1..=self.log {
            self.update(idx >> i);
        }
    }
    // Apply val to the interval [l, r).
    pub fn apply_range(&mut self, l: usize, r: usize, val: F) {
        assert!(l <= r && r <= self.n);
        if l == r {
            return;
        }
        let (l, r) = (l + self.size, r + self.size);
        for i in (1..self.log+1).rev() {
            if ((l >> i) << i) != l {
                self.push(l >> i);
            }
            if ((r >> i) << i) != r {
                self.push((r-1) >> i);
            }
        }
        let (mut a, mut b) = (l, r);
        while a < b {
            if (a & 1) != 0 {
                self.all_apply(a, val);
                a += 1;
            }
            if (b & 1) != 0 {
                b -= 1;
                self.all_apply(b, val);
            }
            a >>= 1; b >>= 1;
        }
        for i in 1..=self.log {
            if ((l >> i) << i) != l {
                self.update(l >> i);
            }
            if ((r >> i) << i) != r {
                self.update((r-1) >> i);
            }
        }
    }
    fn update(&mut self, idx: usize) {
        self.tree[idx] = self.op(self.tree[idx*2], self.tree[idx*2+1]);
    }
    fn all_apply(&mut self, idx: usize, val: F) {
        let mapping = self.mapping;
        self.tree[idx] = mapping(val, self.tree[idx]);
        if idx < self.size {
            self.lazy[idx] = self.composition(val, self.lazy[idx]);
        }
    }
    fn push(&mut self, idx: usize) {
        self.all_apply(idx*2, self.lazy[idx]);
        self.all_apply(idx*2 + 1, self.lazy[idx]);
        self.lazy[idx] = self.id();
    }
    fn op(&self, l: S, r: S) -> S {
        let op = self.op; op(l, r)
    }
    fn e(&self) -> S {
        let e = self.e;
        e()
    }
    fn id(&self) -> F {
        let id = self.id;
        id()
    }
    fn mapping(&self, f: F, x: S) -> S {
        let mapping = self.mapping;
        mapping(f, x)
    }
    fn composition(&self, f: F, g: F) -> F {
        let composition = self.composition;
        composition(f, g)
    }
}
impl<S, F> std::fmt::Debug for LazySegtree<S, F>
where
    S: Copy + Clone + std::fmt::Debug,
    F: Copy + Clone + std::fmt::Debug
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (mut tree, mut lazy, mut l, mut r) = (vec![], vec![], 1, 2);
        while r < self.tree.len() {
            let (mut nd, mut nlz) = (vec![], vec![]);
            for i in l..r {
                nd.push(self.tree[i]);
                nlz.push(self.lazy[i]);
            }
            tree.push(nd);
            lazy.push(nlz);
            l <<= 1;
            r <<= 1;
        }
        write!(f, "tree: {:?}\nlz: {:?}", tree, lazy)
    }
}

pub fn range_add_range_sum_query(size: usize) -> LazySegtree<(i64, i64), i64> {
    LazySegtree::from_vec(
        &vec![(0i64, 1i64); size],
        |l, r| (l.0+r.0, l.1+r.1),
        || (0, 0),
        || 0i64,
        |f, x| (x.0+f*x.1, x.1),
        |f, g| f + g)
}

pub fn range_add_range_maximum_query(size: usize) -> LazySegtree<i64, i64> {
    LazySegtree::from_vec(
        &vec![0i64; size],
        |l, r| std::cmp::max(l, r),
        || std::i64::MIN,
        || 0i64,
        |f, x| f + x,
        |f, g| f + g)
}

pub fn range_add_range_minimum_query(size: usize) -> LazySegtree<i64, i64> {
    LazySegtree::from_vec(
        &vec![0i64; size],
        |l, r| std::cmp::min(l, r),
        || std::i64::MAX,
        || 0i64,
        |f, x| f + x,
        |f, g| f + g)
}


#[cfg(test)]
mod tests {
    use crate::segtree::{
        SegmentTree,
        range_add_range_maximum_query, range_add_range_minimum_query, range_add_range_sum_query
    };

    #[test]
    fn segtree_test() {
        let mut st = SegmentTree::new(10, 0, |l, r| *l + *r);

        let v = [1, 3, 4, 7, 14, 3, 6, 4, 11, 9];
        for (i, w) in v.into_iter().enumerate() {
            st.set(i, w);
        }

        assert_eq!(st.get(0, 10), 62);
        assert_eq!(st.get(5, 10), 33);
        assert_eq!(st.get(0, 5), 29);
        assert_eq!(st.get(3, 7), 30);

        st.set(4, -1);

        assert_eq!(st.get(0, 10), 47);
        assert_eq!(st.get(5, 10), 33);
        assert_eq!(st.get(0, 5), 14);
        assert_eq!(st.get(3, 7), 15);

        st.update_by(4, 15, |old, val| old + val);

        assert_eq!(st.get(0, 10), 62);
        assert_eq!(st.get(5, 10), 33);
        assert_eq!(st.get(0, 5), 29);
        assert_eq!(st.get(3, 7), 30);

        st.update_by(6, 3, |old, val| old * val);

        assert_eq!(st.get(0, 10), 74);
        assert_eq!(st.get(5, 10), 45);
        assert_eq!(st.get(0, 5), 29);
        assert_eq!(st.get(3, 7), 42);
    }

    #[test]
    fn lazy_segtree_test() {
        let v = [1, 3, 4, 7, 14, 3, 6, 4, 11, 9];

        let mut st = range_add_range_maximum_query(10);
        for (i, w) in v.iter().enumerate() {
            st.apply(i, *w);
        }

        assert_eq!(st.prod(0, 10), 14);
        assert_eq!(st.prod(5, 10), 11);
        assert_eq!(st.prod(0, 5), 14);
        assert_eq!(st.prod(5, 8), 6);
        
        let mut st = range_add_range_minimum_query(10);
        for (i, w) in v.iter().enumerate() {
            st.apply(i, *w);
        }

        assert_eq!(st.prod(0, 10), 1);
        assert_eq!(st.prod(5, 10), 3);
        assert_eq!(st.prod(0, 5), 1);
        assert_eq!(st.prod(2, 5), 4);
        
        let mut st = range_add_range_sum_query(10);
        for (i, w) in v.iter().enumerate() {
            st.apply(i, *w);
        }

        assert_eq!(st.prod(0, 10).0, 62);
        assert_eq!(st.prod(5, 10).0, 33);
        assert_eq!(st.prod(0, 5).0, 29);
        assert_eq!(st.prod(3, 7).0, 30);
    }
}