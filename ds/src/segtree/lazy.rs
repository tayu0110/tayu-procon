use std::{
    any::type_name,
    fmt::Debug,
    marker::PhantomData,
    ops::{Add, Mul, Range, RangeBounds},
};

use crate::{convert_range, MapMonoid, ZeroOne};

pub struct LazySegmentTree<M: MapMonoid> {
    n: usize,
    size: usize,
    log: usize,
    tree: Vec<M::M>,
    lazy: Vec<M::Act>,
}

impl<M: MapMonoid> LazySegmentTree<M>
where
    M::M: Clone,
    M::Act: Clone,
{
    pub fn new(size: usize) -> Self {
        LazySegmentTree::from_vec(&vec![M::e(); size])
    }

    pub fn from_vec(v: &[M::M]) -> Self {
        let n = v.len();
        let size = n.next_power_of_two();
        let log = size.trailing_zeros() as usize;
        let mut tree = vec![M::e(); size * 2];
        let lazy = vec![M::id(); size * 2];
        tree.iter_mut()
            .skip(size)
            .zip(v.iter().cloned())
            .for_each(|(t, w)| *t = w);
        for i in (1..size).rev() {
            tree[i] = M::op(&tree[i * 2], &tree[i * 2 + 1]);
        }
        Self { n, size, log, tree, lazy }
    }

    pub fn len(&self) -> usize {
        self.n
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Set `val` to `index`-th element.
    ///
    /// # Panics
    /// - `index < self.len()` must be satisfied.
    pub fn set(&mut self, idx: usize, val: M::M) {
        assert!(idx < self.len());
        let idx = idx + self.size;
        for i in (1..self.log + 1).rev() {
            self.push(idx >> i);
        }
        self.tree[idx] = val;
        for i in 1..=self.log {
            self.update(idx >> i);
        }
    }

    /// Get `index`-th element.
    ///
    /// # Panics
    /// - `index < self.len()` must be satisfied.
    pub fn get(&mut self, idx: usize) -> M::M {
        assert!(idx < self.len());
        let idx = idx + self.size;
        for i in (1..self.log + 1).rev() {
            self.push(idx >> i);
        }
        self.tree[idx].clone()
    }

    /// Apply `M::op` to the elements within `range` and return its result.
    ///
    /// # Panics
    /// - The head of `range` must be smaller than or equal to the tail of `range`.
    /// - `range` must not contain a range greater than `self.len()`.
    pub fn fold(&mut self, range: impl RangeBounds<usize>) -> M::M {
        let Range { start, end } = convert_range(self.len(), range);
        assert!(start <= end);
        assert!(end <= self.len());
        if start == end {
            return M::e();
        }
        let (mut l, mut r) = (start + self.size, end + self.size);
        for i in (1..self.log + 1).rev() {
            if ((l >> i) << i) != l {
                self.push(l >> i);
            }
            if ((r >> i) << i) != r {
                self.push(r >> i);
            }
        }
        let (mut sml, mut smr) = (M::e(), M::e());
        while l < r {
            if l & 1 != 0 {
                sml = M::op(&sml, &self.tree[l]);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                smr = M::op(&self.tree[r], &smr);
            }
            l >>= 1;
            r >>= 1;
        }
        M::op(&sml, &smr)
    }

    pub fn all_prod(&self) -> M::M {
        self.tree[1].clone()
    }

    /// Apply `val` to a point whose `index` is idx.
    fn apply_one(&mut self, idx: usize, val: M::Act) {
        assert!(idx < self.len());
        let idx = idx + self.size;
        for i in (1..self.log + 1).rev() {
            self.push(idx >> i);
        }
        self.tree[idx] = M::map(&self.tree[idx], &val);
        for i in 1..=self.log {
            self.update(idx >> i);
        }
    }

    /// Apply `val` to the elements within `range`.
    pub fn apply(&mut self, range: impl RangeBounds<usize>, val: M::Act) {
        let Range { start, end } = convert_range(self.len(), range);
        assert!(start <= end);
        assert!(end <= self.len());
        if start == end {
            return;
        }
        if end - start == 1 {
            self.apply_one(start, val);
            return;
        }
        let (start, end) = (start + self.size, end + self.size);
        for i in (1..self.log + 1).rev() {
            if ((start >> i) << i) != start {
                self.push(start >> i);
            }
            if ((end >> i) << i) != end {
                self.push((end - 1) >> i);
            }
        }
        let (mut a, mut b) = (start, end);
        while a < b {
            if a & 1 != 0 {
                self.all_apply(a, val.clone());
                a += 1;
            }
            if b & 1 != 0 {
                b -= 1;
                self.all_apply(b, val.clone());
            }
            a >>= 1;
            b >>= 1;
        }
        for i in 1..=self.log {
            if ((start >> i) << i) != start {
                self.update(start >> i);
            }
            if ((end >> i) << i) != end {
                self.update((end - 1) >> i);
            }
        }
    }

    fn update(&mut self, idx: usize) {
        self.tree[idx] = M::op(&self.tree[idx * 2], &self.tree[idx * 2 + 1]);
    }

    fn all_apply(&mut self, idx: usize, val: M::Act) {
        self.tree[idx] = M::map(&self.tree[idx], &val);
        if idx < self.size {
            self.lazy[idx] = M::composite(&val, &self.lazy[idx]);
        }
    }

    fn push(&mut self, idx: usize) {
        self.all_apply(idx * 2, self.lazy[idx].clone());
        self.all_apply(idx * 2 + 1, self.lazy[idx].clone());
        self.lazy[idx] = M::id();
    }
}

impl<M: MapMonoid> Clone for LazySegmentTree<M>
where
    M::M: Clone,
    M::Act: Clone,
{
    fn clone(&self) -> Self {
        Self {
            n: self.n,
            size: self.size,
            log: self.log,
            tree: self.tree.clone(),
            lazy: self.lazy.clone(),
        }
    }
}

impl<M: MapMonoid> Debug for LazySegmentTree<M>
where
    M: MapMonoid,
    M::M: Debug,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct(type_name::<Self>())
            .field("n", &self.n)
            .field("size", &self.size)
            .field("log", &self.log)
            .field("tree", &self.tree)
            .field("lazy", &self.lazy)
            .finish()
    }
}

pub struct RangeAddRangeSumQuery<T>(PhantomData<fn() -> T>);

impl<T> RangeAddRangeSumQuery<T>
where
    T: ZeroOne + Clone + Add<Output = T> + Mul<Output = T>,
{
    pub fn new(size: usize) -> LazySegmentTree<Self> {
        LazySegmentTree::from_vec(&vec![(T::zero(), T::one()); size])
    }
}

impl<T> MapMonoid for RangeAddRangeSumQuery<T>
where
    T: ZeroOne + Clone + Add<Output = T> + Mul<Output = T>,
{
    type M = (T, T);
    type Act = T;

    fn e() -> Self::M {
        (T::zero(), T::zero())
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        (l.0.clone() + r.0.clone(), l.1.clone() + r.1.clone())
    }
    fn id() -> Self::Act {
        T::zero()
    }
    fn composite(l: &Self::Act, r: &Self::Act) -> Self::Act {
        l.clone() + r.clone()
    }
    fn map(elem: &Self::M, act: &Self::Act) -> Self::M {
        (
            elem.0.clone() + act.clone() * elem.1.clone(),
            elem.1.clone(),
        )
    }
}

pub struct RangeAddRangeMaximumQuery;

impl RangeAddRangeMaximumQuery {
    pub fn new(size: usize) -> LazySegmentTree<Self> {
        LazySegmentTree::from_vec(&vec![0; size])
    }
}

impl MapMonoid for RangeAddRangeMaximumQuery {
    type M = i64;
    type Act = i64;

    fn e() -> Self::M {
        i64::MIN
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        *l.max(r)
    }
    fn id() -> Self::Act {
        0
    }
    fn composite(l: &Self::Act, r: &Self::Act) -> Self::Act {
        l + r
    }
    fn map(elem: &Self::M, act: &Self::Act) -> Self::M {
        act + elem
    }
}

pub struct RangeAddRangeMinimumQuery;

impl RangeAddRangeMinimumQuery {
    pub fn new(size: usize) -> LazySegmentTree<Self> {
        LazySegmentTree::from_vec(&vec![0; size])
    }
}

impl MapMonoid for RangeAddRangeMinimumQuery {
    type M = i64;
    type Act = i64;

    fn e() -> Self::M {
        i64::MAX
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        *l.min(r)
    }
    fn id() -> Self::Act {
        0
    }
    fn composite(l: &Self::Act, r: &Self::Act) -> Self::Act {
        l + r
    }
    fn map(elem: &Self::M, act: &Self::Act) -> Self::M {
        act + elem
    }
}

pub struct RangeAffineRangeSum<T>(PhantomData<fn() -> T>);

impl<T> RangeAffineRangeSum<T>
where
    T: ZeroOne + Clone + Add<Output = T> + Mul<Output = T>,
{
    pub fn new(a: Vec<T>) -> LazySegmentTree<Self> {
        let a = a.into_iter().map(|v| (v, T::one())).collect::<Vec<_>>();
        LazySegmentTree::from_vec(&a)
    }
}

impl<T> MapMonoid for RangeAffineRangeSum<T>
where
    T: ZeroOne + Clone + Add<Output = T> + Mul<Output = T>,
{
    type M = (T, T);
    type Act = (T, T);

    fn e() -> Self::M {
        (T::zero(), T::zero())
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        (l.0.clone() + r.0.clone(), l.1.clone() + r.1.clone())
    }
    fn id() -> Self::Act {
        (T::one(), T::zero())
    }
    fn composite(l: &Self::Act, r: &Self::Act) -> Self::Act {
        (
            l.0.clone() * r.0.clone(),
            l.0.clone() * r.1.clone() + l.1.clone(),
        )
    }
    fn map(elem: &Self::M, act: &Self::Act) -> Self::M {
        (
            act.0.clone() * elem.0.clone() + act.1.clone() * elem.1.clone(),
            elem.1.clone(),
        )
    }
}

pub struct RangeFlipRangeLongestTerm;

impl RangeFlipRangeLongestTerm {
    pub fn new(v: &[bool]) -> LazySegmentTree<Self> {
        LazySegmentTree::from_vec(
            &v.iter()
                .map(|&f| {
                    let f = f as u32;
                    (f, f, f, 1, 1 - f, 1 - f, 1 - f)
                })
                .collect::<Vec<_>>(),
        )
    }
}

impl MapMonoid for RangeFlipRangeLongestTerm {
    type M = (u32, u32, u32, u32, u32, u32, u32);
    type Act = bool;

    fn e() -> Self::M {
        (0, 0, 0, 0, 1, 1, 1)
    }
    fn op(l: &Self::M, r: &Self::M) -> Self::M {
        let (rm, rl, rr, rt, rm0, rl0, rr0) = r;
        let (m, l, r, t, m0, l0, r0) = l;
        (
            *rm.max(m).max(&(r + rl)),
            if l == t { l + rl } else { *l },
            if rr == rt { rr + r } else { *rr },
            t + rt,
            *rm0.max(m0).max(&(r0 + rl0)),
            if l0 == t { l0 + rl0 } else { *l0 },
            if rr0 == rt { rr0 + r0 } else { *rr0 },
        )
    }
    fn id() -> Self::Act {
        false
    }
    fn composite(l: &Self::Act, r: &Self::Act) -> Self::Act {
        l ^ r
    }
    fn map(elem: &Self::M, act: &Self::Act) -> Self::M {
        if !act {
            return *elem;
        }
        let (m, l, r, t, m0, l0, r0) = elem;
        (*m0, *l0, *r0, *t, *m, *l, *r)
    }
}
