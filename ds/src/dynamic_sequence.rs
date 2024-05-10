use std::cell::{Cell, RefCell, RefMut};
use std::fmt::Debug;
use std::ops::{Bound, Range, RangeBounds};
use std::ptr::copy;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::splay_tree::NodeAllocator;
use crate::{
    splay_tree::{NodeData, NodeRef},
    DefaultZST, MapMonoid,
};

static DATA_INDEX: AtomicUsize = AtomicUsize::new(0);

fn convert_range(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    let start = match range.start_bound() {
        Bound::Included(l) => *l,
        Bound::Unbounded => 0,
        _ => unreachable!(),
    };
    let end = match range.end_bound() {
        Bound::Included(r) => r + 1,
        Bound::Excluded(r) => *r,
        Bound::Unbounded => len,
    };
    Range { start, end }
}

struct DSData<M: MapMonoid> {
    // 62-bit   : has lazy flag
    // 63-bit   : reverse flag
    index: usize,
    size: usize,
    val: M::M,
    sum: M::M,
    lazy: M::Act,
}

impl<M: MapMonoid> DSData<M> {
    fn new() -> Self {
        let index = DATA_INDEX.fetch_add(1, Ordering::Relaxed);
        assert!(index < 1 << 62);
        Self { index, size: 1, val: M::e(), sum: M::e(), lazy: M::id() }
    }

    fn with_value(val: M::M) -> Self {
        let mut res = Self::new();
        res.val = val;
        res.update(None, None);
        res
    }

    const fn is_reversed(&self) -> bool {
        self.index >= 1 << 63
    }

    const fn has_lazy(&self) -> bool {
        // also return true if `is reverse` flag is true
        self.index >= 1 << 62
    }

    fn set_lazy(&mut self, act: &M::Act) {
        if self.has_lazy() {
            self.lazy = M::composite(&self.lazy, act);
        } else {
            self.index |= 1 << 62;
            unsafe { copy(act as _, &mut self.lazy as _, 1) }
        }
    }
}

impl<M: MapMonoid> NodeData for DSData<M> {
    fn index(&self) -> usize {
        self.index & !(0b11 << 62)
    }

    fn propagate(&mut self, left: Option<NodeRef<Self>>, right: Option<NodeRef<Self>>) {
        if self.has_lazy() {
            if let Some(mut left) = left {
                left.data.val = M::map(&left.data.val, &self.lazy);
                left.data.sum = M::map(&left.data.sum, &self.lazy);
                left.data.set_lazy(&self.lazy);
                if self.is_reversed() {
                    left.toggle();
                }
            }
            if let Some(mut right) = right {
                right.data.val = M::map(&right.data.val, &self.lazy);
                right.data.sum = M::map(&right.data.sum, &self.lazy);
                right.data.set_lazy(&self.lazy);
                if self.is_reversed() {
                    right.toggle();
                }
            }
            self.lazy = M::id();
            self.index = self.index();
        }
    }

    fn update(&mut self, left: Option<NodeRef<Self>>, right: Option<NodeRef<Self>>) {
        match (left, right) {
            (Some(l), Some(r)) => {
                self.size = l.data.size + r.data.size + 1;
                self.sum = M::op(&M::op(&l.data.sum, &self.val), &r.data.sum)
            }
            (Some(l), _) => {
                self.size = l.data.size + 1;
                self.sum = M::op(&l.data.sum, &self.val)
            }
            (_, Some(r)) => {
                self.size = r.data.size + 1;
                self.sum = M::op(&self.val, &r.data.sum)
            }
            _ => {
                self.size = 1;
                unsafe { copy(&self.val as _, &mut self.sum as _, 1) }
            }
        };
    }

    fn aggrmove(&mut self, source: NodeRef<Self>) {
        self.size = source.data.size;
        unsafe { copy(&source.data.sum as _, &mut self.sum as _, 1) }
    }
}

impl<M: MapMonoid> PartialEq for DSData<M> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<M> Debug for DSData<M>
where
    M: MapMonoid,
    M::M: Debug,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DSData")
            .field("index", &self.index())
            .field("size", &self.size)
            .field("val", &self.val)
            .field("sum", &self.sum)
            .field("lazy", &self.lazy)
            .finish()
    }
}

impl<M: MapMonoid> Default for DSData<M> {
    fn default() -> Self {
        Self::new()
    }
}

impl<M: MapMonoid> NodeRef<DSData<M>> {
    fn toggle(mut self) {
        self.data.index ^= 1 << 63;
        M::reverse(&mut self.data.sum);
        (self.left, self.right) = (self.right, self.left);
    }
}

pub struct DynamicSequence<M: MapMonoid = DefaultZST> {
    root: Cell<Option<NodeRef<DSData<M>>>>,
    alloc: Rc<RefCell<NodeAllocator<DSData<M>>>>,
}

impl<M: MapMonoid> DynamicSequence<M> {
    /// Generate a new `DynamicSequence`.
    ///
    /// Each value of elements are initialize by `MapMonoid::e()`.
    pub fn new(size: usize) -> Self {
        (0..size).map(|_| M::e()).collect()
    }

    /// Return the length of this sequence.
    ///
    /// # Examples
    /// ```
    /// use ds::DynamicSequence;
    ///
    /// let mut dc = <DynamicSequence>::new(5);
    /// assert_eq!(dc.len(), 5);
    ///
    /// dc.insert(0, ());
    /// assert_eq!(dc.len(), 6);
    ///
    /// dc.remove(0);
    /// dc.remove(1);
    /// assert_eq!(dc.len(), 4);
    /// ```
    pub fn len(&self) -> usize {
        self.root.get().map_or(0, |r| r.data.size)
    }

    /// Check if `self.len()` is zero.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn convert_range(&self, range: impl RangeBounds<usize>) -> Range<usize> {
        let res = convert_range(self.len(), range);
        assert!(res.start <= res.end && res.end <= self.len() && res.start <= self.len());
        res
    }

    /// Return n-th node. Returned Node will be new root of inner Splay Tree.
    fn nth_node(&self, n: usize) -> Option<NodeRef<DSData<M>>> {
        let mut node = self.root.get()?;
        (n < node.data.size).then(|| {
            let mut rem = n + 1;
            loop {
                node.propagate();
                if let Some(left) = node.left {
                    if left.data.size >= rem {
                        node = left;
                        continue;
                    }

                    rem -= left.data.size;
                }

                if rem == 1 {
                    node.splay();
                    debug_assert_eq!(node.left.map_or(0, |l| l.data.size), n);
                    self.root.set(Some(node));
                    break node;
                }

                rem -= 1;
                node = node.right.expect("Inconsistent node size");
            }
        })
    }

    /// Although this process is required internally in an immutable method,
    /// it should be exposed externally as a variable method, so the method is split.
    fn split_off_inner(&self, at: usize) -> DynamicSequence<M> {
        if at == 0 {
            return Self {
                root: Cell::new(self.root.take()),
                alloc: Rc::clone(&self.alloc),
            };
        }
        if at == self.len() {
            return Self { root: Cell::new(None), alloc: Rc::clone(&self.alloc) };
        }

        let mut back = self
            .nth_node(at)
            .unwrap_or_else(|| panic!("`self.len()` is {}, but `at` is {at}", self.len()));
        let front = back.disconnect_left();
        back.update();
        self.root.set(front);
        Self { root: Cell::new(Some(back)), alloc: Rc::clone(&self.alloc) }
    }

    /// Split and Return the partition after the `at`th of the sequence.  
    /// The `self` is changed so that the elements after `at` are deleted.
    ///
    /// # Panics
    /// - `at < self.len()` must be satisfied.
    ///
    /// # Examples
    /// ```
    /// use ds::DynamicSequence;
    ///
    /// let mut dc = <DynamicSequence>::new(5);
    /// let back = dc.split_off(3);
    /// assert_eq!(dc.len(), 3);
    /// assert_eq!(back.len(), 2);
    ///
    /// let back = dc.split_off(0);
    /// assert!(dc.is_empty());
    /// assert_eq!(back.len(), 3);
    /// ```
    pub fn split_off(&mut self, at: usize) -> DynamicSequence<M> {
        self.split_off_inner(at)
    }

    /// Although this process is required internally in an immutable method,
    /// it should be exposed externally as a variable method, so the method is split.
    fn extend_inner(&self, other: Self) {
        let Some(other) = other.root.take() else {
            return;
        };

        let Some(mut root) = self.last_node() else {
            self.root.set(Some(other));
            return;
        };
        root.connect_right(other);
        root.update();
        self.root.set(Some(root));
    }

    /// Extend `self` by `other`.
    ///
    /// # Examples
    /// ```
    /// use ds::DynamicSequence;
    ///
    /// let mut dc = <DynamicSequence>::new(3);
    /// assert_eq!(dc.len(), 3);
    /// dc.extend(DynamicSequence::new(3));
    /// assert_eq!(dc.len(), 6);
    /// ```
    pub fn extend(&mut self, other: Self) {
        self.extend_inner(other);
    }

    /// Insert `element` as `at`th element.  
    /// If `at` is equal to `self.len()`, `element` is pushed as last element.
    ///
    /// # Panics
    /// - `at <= self.len()` must be satisfied.
    ///
    /// # Examples
    /// ```
    /// use ds::{DynamicSequence, MapMonoid};
    ///
    /// struct T;
    /// impl MapMonoid for T {
    ///     type M = u32;
    ///     type Act = ();
    ///     fn e() -> u32 { 0 }
    ///     fn op(l: &u32, r: &u32) -> u32 { 0 }
    ///     fn id() {}
    ///     fn composite(_: &(), _: &()) {}
    ///     fn map(m: &u32, _: &()) -> u32 { *m }
    /// }
    ///
    /// // [0, 1, 2, 3, 4]
    /// let mut dc = (0..5).collect::<DynamicSequence<T>>();
    /// // [0, 5, 1, 2, 3, 4]
    /// dc.insert(1, 5);
    /// // [0, 5, 1, 2, 3, 4, 6]
    /// dc.insert(6, 6);
    ///
    /// assert_eq!(dc.into_iter().collect::<Vec<_>>(), vec![0, 5, 1, 2, 3, 4, 6]);
    /// ```
    pub fn insert(&mut self, at: usize, element: M::M) {
        assert!(at <= self.len());

        let new = self.alloc.borrow_mut().alloc(DSData::with_value(element));
        let mid = Self { root: Cell::new(Some(new)), alloc: Rc::clone(&self.alloc) };
        let back = self.split_off(at);
        self.extend(mid);
        self.extend(back);
    }

    fn first_node(&self) -> Option<NodeRef<DSData<M>>> {
        let mut node = self.root.get()?;
        node.propagate();
        while let Some(left) = node.left {
            node = left;
            node.propagate();
        }
        node.splay();
        Some(node)
    }

    fn last_node(&self) -> Option<NodeRef<DSData<M>>> {
        let mut node = self.root.get()?;
        node.propagate();
        while let Some(right) = node.right {
            node = right;
            node.propagate();
        }
        node.splay();
        Some(node)
    }

    /// Pop the first element of this sequence.
    /// If `self.is_empty()` is `true`, return None.
    ///
    /// # Examples
    /// ```
    /// use ds::{DynamicSequence, MapMonoid};
    ///
    /// struct T;
    /// impl MapMonoid for T {
    ///     type M = u32;
    ///     type Act = ();
    ///     fn e() -> u32 { 0 }
    ///     fn op(l: &u32, r: &u32) -> u32 { 0 }
    ///     fn id() {}
    ///     fn composite(_: &(), _: &()) {}
    ///     fn map(m: &u32, _: &()) -> u32 { *m }
    /// }
    ///
    /// // [0, 1, 2]
    /// let mut dc = (0..3).collect::<DynamicSequence<T>>();
    /// assert_eq!(dc.pop_first(), Some(0));
    /// assert_eq!(dc.pop_first(), Some(1));
    /// assert_eq!(dc.pop_first(), Some(2));
    /// assert_eq!(dc.pop_first(), None);
    /// ```
    pub fn pop_first(&mut self) -> Option<M::M> {
        let mut root = self.first_node()?;
        self.root.set(root.disconnect_right());
        let data = std::mem::take(&mut root.data);
        self.alloc.borrow_mut().dealloc(root);
        Some(data.val)
    }

    /// Pop the last element of this sequence.
    /// If `self.is_empty()` is `true`, return None.
    ///
    /// # Examples
    /// ```
    /// use ds::{DynamicSequence, MapMonoid};
    ///
    /// struct T;
    /// impl MapMonoid for T {
    ///     type M = u32;
    ///     type Act = ();
    ///     fn e() -> u32 { 0 }
    ///     fn op(l: &u32, r: &u32) -> u32 { 0 }
    ///     fn id() {}
    ///     fn composite(_: &(), _: &()) {}
    ///     fn map(m: &u32, _: &()) -> u32 { *m }
    /// }
    ///
    /// // [0, 1, 2]
    /// let mut dc = (0..3).collect::<DynamicSequence<T>>();
    /// assert_eq!(dc.pop_last(), Some(2));
    /// assert_eq!(dc.pop_last(), Some(1));
    /// assert_eq!(dc.pop_last(), Some(0));
    /// assert_eq!(dc.pop_last(), None);
    /// ```
    pub fn pop_last(&mut self) -> Option<M::M> {
        let mut root = self.last_node()?;
        self.root.set(root.disconnect_left());
        let data = std::mem::take(&mut root.data);
        self.alloc.borrow_mut().dealloc(root);
        Some(data.val)
    }

    /// Remove `at`th element from this sequence.
    ///
    /// # Panics
    /// - `at < self.len()` must be satisfied.
    ///
    /// # Examples
    /// ```
    /// use ds::{DynamicSequence, MapMonoid};
    ///
    /// struct T;
    /// impl MapMonoid for T {
    ///     type M = u32;
    ///     type Act = ();
    ///     fn e() -> u32 { 0 }
    ///     fn op(l: &u32, r: &u32) -> u32 { 0 }
    ///     fn id() {}
    ///     fn composite(_: &(), _: &()) {}
    ///     fn map(m: &u32, _: &()) -> u32 { *m }
    /// }
    ///
    /// // [0, 1, 2]
    /// let mut dc = (0..3).collect::<DynamicSequence<T>>();
    /// assert_eq!(dc.remove(1), 1);
    /// assert_eq!(dc.remove(1), 2);
    /// ```
    pub fn remove(&mut self, at: usize) -> M::M {
        assert!(at < self.len());

        let mut back = self.split_off(at);
        let res = back.pop_first().unwrap();
        self.extend(back);
        res
    }

    /// Reverse the range of subsequence specified by `range`.
    ///
    /// # Panics
    /// - `at < self.len()` must be satisfied.
    ///
    /// # Examples
    /// ```
    /// use ds::{DynamicSequence, MapMonoid};
    ///
    /// struct T;
    /// impl MapMonoid for T {
    ///     type M = u32;
    ///     type Act = ();
    ///     fn e() -> u32 { 0 }
    ///     fn op(l: &u32, r: &u32) -> u32 { 0 }
    ///     fn id() {}
    ///     fn composite(_: &(), _: &()) {}
    ///     fn map(m: &u32, _: &()) -> u32 { *m }
    /// }
    ///
    /// // [0, 1, 2, 3, 4, 5]
    /// let mut dc = (0..6).collect::<DynamicSequence<T>>();
    /// // [0, 2, 1, 3, 4, 5]
    /// dc.reverse(1..3);
    /// // [0, 2, 5, 4, 3, 1]
    /// dc.reverse(2..);
    /// assert_eq!(dc.into_iter().collect::<Vec<_>>(), vec![0, 2, 5, 4, 3, 1]);
    /// ```
    pub fn reverse(&mut self, range: impl RangeBounds<usize>) {
        if self.is_empty() {
            return;
        }
        let range = self.convert_range(range);
        if range.len() <= 1 {
            return;
        }

        let back = self.split_off(range.end);
        let mid = self.split_off(range.start);

        let mut root = mid.root.get().unwrap();
        root.toggle();
        root.propagate();

        self.extend(mid);
        self.extend(back);
    }

    /// Overwrite `at`th element to `val`.
    pub fn set(&mut self, at: usize, val: M::M) {
        let mut n = self.nth_node(at).unwrap();
        n.data.val = val;
        n.update();
        self.root.set(Some(n));
    }

    /// Update `at`th element by `f`.
    pub fn update_by(&mut self, at: usize, f: impl Fn(&M::M) -> M::M) {
        let mut n = self.nth_node(at).unwrap();
        n.data.val = f(&n.data.val);
        n.update();
        self.root.set(Some(n));
    }

    /// Apply `act` to the range of subsequence specified by `range`.
    pub fn apply_range(&mut self, range: impl RangeBounds<usize>, act: &M::Act) {
        if self.is_empty() {
            return;
        }
        let range = self.convert_range(range);
        if range.is_empty() {
            return;
        }
        if range.len() == 1 {
            self.update_by(range.start, |m| M::map(m, act));
            return;
        }

        let back = self.split_off(range.end);
        let mid = self.split_off(range.start);
        let mut root = mid.root.get().unwrap();
        root.data.val = M::map(&root.data.val, act);
        root.data.sum = M::map(&root.data.sum, act);
        root.data.set_lazy(act);
        root.propagate();
        self.extend(mid);
        self.extend(back);
    }

    /// Fold values of the range of subsequence specified by `range`.
    pub fn fold(&self, range: impl RangeBounds<usize>) -> M::M {
        if self.is_empty() {
            return M::e();
        }

        let range = self.convert_range(range);
        if range.is_empty() {
            return M::e();
        }
        if range.len() == self.len() {
            return M::op(&M::e(), &self.root.get().unwrap().data.sum);
        }

        let back = self.split_off_inner(range.end);
        let mid = self.split_off_inner(range.start);
        let res = M::op(&M::e(), &mid.root.get().unwrap().data.sum);
        self.extend_inner(mid);
        self.extend_inner(back);
        res
    }

    pub fn iter(&self) -> Iter<'_, M> {
        Iter { seq: self, node: self.first_node() }
    }
}

impl<M> Debug for DynamicSequence<M>
where
    M: MapMonoid,
    M::M: Debug,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DynamicSequence")
            .field("root", &self.root.get())
            .finish()
    }
}

impl<M: MapMonoid> Default for DynamicSequence<M> {
    fn default() -> Self {
        Self {
            root: Cell::new(None),
            alloc: Rc::new(RefCell::new(NodeAllocator::default())),
        }
    }
}

impl<M: MapMonoid> Drop for DynamicSequence<M> {
    fn drop(&mut self) {
        fn dealloc_recursive<M: MapMonoid>(
            node: Option<NodeRef<DSData<M>>>,
            alloc: &mut RefMut<NodeAllocator<DSData<M>>>,
        ) -> Option<()> {
            let node = node?;
            dealloc_recursive(node.left, alloc);
            dealloc_recursive(node.right, alloc);
            alloc.dealloc(node);
            Some(())
        }
        if Rc::strong_count(&self.alloc) > 1 {
            dealloc_recursive(self.root.take(), &mut self.alloc.borrow_mut());
        }
    }
}

impl<M: MapMonoid> FromIterator<M::M> for DynamicSequence<M> {
    fn from_iter<T: IntoIterator<Item = M::M>>(iter: T) -> Self {
        let mut alloc = NodeAllocator::default();
        Self {
            root: Cell::new(
                iter.into_iter()
                    .map(|val| alloc.alloc(DSData::with_value(val)))
                    .reduce(|s, mut v| {
                        v.connect_left(s);
                        v.update();
                        v
                    }),
            ),
            alloc: Rc::new(RefCell::new(alloc)),
        }
    }
}

pub struct Iter<'a, M: MapMonoid> {
    seq: &'a DynamicSequence<M>,
    node: Option<NodeRef<DSData<M>>>,
}

impl<'a, M: MapMonoid> Iterator for Iter<'a, M> {
    type Item = M::M;
    fn next(&mut self) -> Option<Self::Item> {
        let mut node = self.node.take()?;
        if !node.is_root() {
            node.splay();
        }
        let res = M::op(&M::e(), &node.data.val);
        if let Some(mut next) = node.right {
            node.propagate();
            next.propagate();
            while let Some(n) = next.left {
                next = n;
                next.propagate();
            }
            node.splay();
            self.node = Some(next);
            self.seq.root.set(Some(next));
        }
        Some(res)
    }
}

pub struct IntoIter<M: MapMonoid> {
    seq: DynamicSequence<M>,
}

impl<M: MapMonoid> Iterator for IntoIter<M> {
    type Item = M::M;
    fn next(&mut self) -> Option<Self::Item> {
        self.seq.pop_first()
    }
}

impl<M: MapMonoid> DoubleEndedIterator for IntoIter<M> {
    fn next_back(&mut self) -> Option<Self::Item> {
        self.seq.pop_last()
    }
}

impl<M: MapMonoid> IntoIterator for DynamicSequence<M> {
    type Item = M::M;
    type IntoIter = IntoIter<M>;
    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter { seq: self }
    }
}

#[cfg(test)]
mod tests {
    use rand::{thread_rng, Rng};
    use static_modint::{Mod998244353, StaticModint};

    use super::*;

    type Modint = StaticModint<Mod998244353>;

    struct M32Affine;

    impl MapMonoid for M32Affine {
        type M = (Modint, Modint);
        type Act = (Modint, Modint);
        fn e() -> Self::M {
            (Modint::zero(), Modint::zero())
        }
        fn op(l: &Self::M, r: &Self::M) -> Self::M {
            (l.0 + r.0, l.1 + r.1)
        }
        fn id() -> Self::Act {
            (Modint::one(), Modint::zero())
        }
        fn composite(l: &Self::Act, r: &Self::Act) -> Self::Act {
            (r.0 * l.0, r.0 * l.1 + r.1)
        }
        fn map(m: &Self::M, act: &Self::Act) -> Self::M {
            (act.0 * m.0 + act.1 * m.1, m.1)
        }
    }

    #[test]
    fn random_query_test() {
        const V: usize = 3;

        let mut rng = thread_rng();

        for i in 0..10000 {
            eprintln!("----- start {i} iteration -----");
            let mut ds = (0..V)
                .map(|_| (Modint::zero(), Modint::one()))
                .collect::<DynamicSequence<M32Affine>>();
            let mut t = vec![Modint::zero(); V];
            for _ in 0..10 {
                let ty = rng.gen_range(0u8..5);
                match (t.is_empty(), ty) {
                    (true, _) | (_, 0) => {
                        let i = rng.gen_range(0..=t.len());
                        let x = rng.gen_range(0..10);
                        eprintln!("ty: {ty}, i: {i}, x: {x}");
                        ds.insert(i, (Modint::new(x), Modint::one()));
                        t.insert(i, Modint::new(x));
                    }
                    (_, 1) => {
                        let i = rng.gen_range(0..t.len());
                        eprintln!("ty: {ty}, i: {i}");
                        assert_eq!(ds.remove(i).0, t.remove(i));
                    }
                    (_, 2) => {
                        let l = rng.gen_range(0..t.len());
                        let r = rng.gen_range(l + 1..=t.len());
                        eprintln!("ty: {ty}, l: {l}, r: {r}");
                        t[l..r].reverse();
                        ds.reverse(l..r);
                    }
                    (_, 3) => {
                        let l = rng.gen_range(0..t.len());
                        let r = rng.gen_range(l + 1..=t.len());
                        let b = rng.gen_range(0..5);
                        let c = rng.gen_range(0..5);
                        eprintln!("ty: {ty}, l: {l}, r: {r}, b: {b}, c: {c}");
                        ds.apply_range(l..r, &(Modint::new(b), Modint::new(c)));
                        t[l..r]
                            .iter_mut()
                            .for_each(|t| *t = Modint::new(b) * *t + Modint::new(c));
                    }
                    (_, 4) => {
                        let l = rng.gen_range(0..t.len());
                        let r = rng.gen_range(l + 1..=t.len());
                        eprintln!("ty: {ty}, l: {l}, r: {r}");
                        assert_eq!(
                            ds.fold(l..r).0,
                            t[l..r].iter().fold(Modint::zero(), |s, v| s + *v)
                        );
                    }
                    _ => {}
                }

                eprintln!(
                    "t: {t:?}, ds: {:?}",
                    ds.iter().map(|v| v.0).collect::<Vec<_>>()
                );
                assert_eq!(t, ds.iter().map(|v| v.0).collect::<Vec<_>>());
            }
        }
    }
}
