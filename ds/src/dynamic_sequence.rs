use std::cell::{Cell, RefCell, RefMut};
use std::fmt::Debug;
use std::ops::{Bound, Range, RangeBounds};
use std::ptr::copy;
use std::rc::Rc;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::convert_range;
use crate::splay_tree::{Node, NodeAllocator};
use crate::{
    splay_tree::{NodeData, NodeRef},
    DefaultZST, MapMonoid,
};

static DATA_INDEX: AtomicUsize = AtomicUsize::new(0);

struct DSData<M: MapMonoid> {
    // 62-bit   : has lazy flag
    // 63-bit   : reverse flag
    index: usize,
    size: usize,
    val: M::M,
    sum: M::M,
    lazy: M::Act,
}

impl<M> DSData<M>
where
    M: MapMonoid,
    M::M: Clone,
{
    fn new() -> Self {
        let index = DATA_INDEX.fetch_add(1, Ordering::Relaxed);
        assert!(index < 1 << 62);
        Self { index, size: 1, val: M::e(), sum: M::e(), lazy: M::id() }
    }

    fn with_value(val: M::M) -> Self {
        let mut res = Self::new();
        res.val = val;
        res.sum = res.val.clone();
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

impl<M> NodeData for DSData<M>
where
    M: MapMonoid,
    M::M: Clone,
{
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
                self.sum = self.val.clone();
            }
        };
    }

    fn aggrmove(&mut self, source: NodeRef<Self>) {
        self.size = source.data.size;
        self.sum = source.data.sum.clone();
    }

    fn toggle(&mut self) {
        self.index ^= 1 << 63;
        M::reverse(&mut self.sum);
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
    M::M: Debug + Clone,
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

impl<M> Default for DSData<M>
where
    M: MapMonoid,
    M::M: Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

pub struct DynamicSequence<M: MapMonoid = DefaultZST>
where
    M::M: Clone,
{
    root: Cell<Option<NodeRef<DSData<M>>>>,
    alloc: Rc<RefCell<NodeAllocator<DSData<M>>>>,
}

impl<M> DynamicSequence<M>
where
    M: MapMonoid,
    M::M: Clone,
{
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
                if let Some(left) = node.left() {
                    if left.data.size >= rem {
                        node = left;
                        continue;
                    }

                    rem -= left.data.size;
                }

                if rem == 1 {
                    node.splay();
                    debug_assert_eq!(node.left().map_or(0, |l| l.data.size), n);
                    self.root.set(Some(node));
                    break node;
                }

                rem -= 1;
                node = node.right().expect("Inconsistent node size");
            }
        })
    }

    pub fn get(&self, nth: usize) -> Option<&M::M> {
        unsafe { Some(&self.nth_node(nth)?.0.as_ref().data.val) }
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
    fn append_inner(&self, other: Self) {
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
    /// # Note
    /// `extend` can perform the same operation, but `append` is more efficient.  
    /// Specifically, `append` is logarithmic time with respect to the number of elements and `extend` is linear time.
    ///
    /// # Examples
    /// ```
    /// use ds::DynamicSequence;
    ///
    /// let mut dc = <DynamicSequence>::new(3);
    /// assert_eq!(dc.len(), 3);
    /// dc.append(DynamicSequence::new(3));
    /// assert_eq!(dc.len(), 6);
    /// ```
    pub fn append(&mut self, other: Self) {
        self.append_inner(other);
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
        self.append(mid);
        self.append(back);
    }

    fn first_node(&self) -> Option<NodeRef<DSData<M>>> {
        let mut node = self.root.get()?;
        node.propagate();
        while let Some(left) = node.left() {
            node = left;
            node.propagate();
        }
        node.splay();
        self.root.set(Some(node));
        Some(node)
    }

    fn last_node(&self) -> Option<NodeRef<DSData<M>>> {
        let mut node = self.root.get()?;
        node.propagate();
        while let Some(right) = node.right() {
            node = right;
            node.propagate();
        }
        node.splay();
        Some(node)
    }

    /// Push element from the head of this sequence.
    pub fn push_first(&mut self, element: M::M) {
        self.insert(0, element);
    }

    /// Push element from the tail of this sequence.
    pub fn push_last(&mut self, element: M::M) {
        self.insert(self.len(), element);
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
        self.append(back);
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
    pub fn update_by(&mut self, at: usize, mut f: impl FnMut(&M::M) -> M::M) {
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
        self.append_inner(mid);
        self.append_inner(back);
        res
    }

    pub fn iter(&self) -> Iter<'_, M> {
        Iter { seq: self, node: self.first_node() }
    }
}

impl<M> Debug for DynamicSequence<M>
where
    M: MapMonoid,
    M::M: Debug + Clone,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DynamicSequence")
            .field("root", &self.root.get())
            .finish()
    }
}

impl<M> Clone for DynamicSequence<M>
where
    M: MapMonoid,
    M::M: Clone,
    M::Act: Clone,
{
    fn clone(&self) -> Self {
        let mut cloned = Self { root: Cell::new(None), alloc: Rc::clone(&self.alloc) };
        cloned.extend(self.iter().cloned());
        cloned
    }
}

impl<M> Extend<M::M> for DynamicSequence<M>
where
    M: MapMonoid,
    M::M: Clone,
{
    fn extend<T: IntoIterator<Item = M::M>>(&mut self, iter: T) {
        iter.into_iter().for_each(|e| self.push_last(e));
    }
}

impl<M> Default for DynamicSequence<M>
where
    M: MapMonoid,
    M::M: Clone,
{
    fn default() -> Self {
        Self {
            root: Cell::new(None),
            alloc: Rc::new(RefCell::new(NodeAllocator::default())),
        }
    }
}

impl<M> Drop for DynamicSequence<M>
where
    M: MapMonoid,
    M::M: Clone,
{
    fn drop(&mut self) {
        fn dealloc_recursive<M>(
            node: Option<NodeRef<DSData<M>>>,
            alloc: &mut RefMut<NodeAllocator<DSData<M>>>,
        ) -> Option<()>
        where
            M: MapMonoid,
            M::M: Clone,
        {
            let node = node?;
            dealloc_recursive(node.disconnect_left(), alloc);
            dealloc_recursive(node.disconnect_right(), alloc);
            alloc.dealloc(node);
            Some(())
        }
        if Rc::strong_count(&self.alloc) > 1 {
            dealloc_recursive(self.root.take(), &mut self.alloc.borrow_mut());
        }
    }
}

impl<M> FromIterator<M::M> for DynamicSequence<M>
where
    M: MapMonoid,
    M::M: Clone,
{
    fn from_iter<T: IntoIterator<Item = M::M>>(iter: T) -> Self {
        let buf = iter
            .into_iter()
            .map(|val| Node::new(DSData::with_value(val)))
            .collect::<Box<[Node<DSData<M>>]>>();
        let len = buf.len();
        let mut alloc = NodeAllocator::from_buffer(buf);
        Self {
            root: Cell::new(
                (0..len)
                    .map(|_| alloc.alloc_uninitialized())
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

#[derive(Clone)]
pub struct Iter<'a, M: MapMonoid>
where
    M::M: Clone,
{
    seq: &'a DynamicSequence<M>,
    node: Option<NodeRef<DSData<M>>>,
}

impl<'a, M> Iterator for Iter<'a, M>
where
    M: MapMonoid,
    M::M: Clone,
{
    type Item = &'a M::M;
    fn next(&mut self) -> Option<Self::Item> {
        let mut node = self.node.take()?;
        if !node.is_root() {
            node.splay();
        }
        let res = unsafe { &node.0.as_ref().data.val };
        if let Some(mut next) = node.right() {
            node.propagate();
            next.propagate();
            while let Some(n) = next.left() {
                next = n;
                next.propagate();
            }
            next.splay();
            self.node = Some(next);
            self.seq.root.set(Some(next));
        }
        Some(res)
    }
}

pub struct IntoIter<M: MapMonoid>
where
    M::M: Clone,
{
    seq: DynamicSequence<M>,
}

impl<M> Clone for IntoIter<M>
where
    M: MapMonoid,
    M::M: Clone,
    M::Act: Clone,
{
    fn clone(&self) -> Self {
        Self { seq: self.seq.clone() }
    }
}

impl<M> Iterator for IntoIter<M>
where
    M: MapMonoid,
    M::M: Clone,
{
    type Item = M::M;
    fn next(&mut self) -> Option<Self::Item> {
        self.seq.pop_first()
    }
}

impl<M> DoubleEndedIterator for IntoIter<M>
where
    M: MapMonoid,
    M::M: Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        self.seq.pop_last()
    }
}

impl<M> IntoIterator for DynamicSequence<M>
where
    M: MapMonoid,
    M::M: Clone,
{
    type Item = M::M;
    type IntoIter = IntoIter<M>;
    fn into_iter(self) -> Self::IntoIter {
        Self::IntoIter { seq: self }
    }
}

pub struct DynamicSortedSequence<M: MapMonoid>
where
    M::M: Clone,
{
    seq: DynamicSequence<M>,
}

impl<M: MapMonoid> DynamicSortedSequence<M>
where
    M::M: Ord + Clone,
{
    /// Create new dynamic sorted sequence.
    pub fn new() -> Self {
        Self { seq: DynamicSequence::new(0) }
    }

    /// Return the elements owned by this sequence.
    pub fn len(&self) -> usize {
        self.seq.len()
    }

    /// Check if `self.len() == 0` is satisfied.
    pub fn is_empty(&self) -> bool {
        self.seq.is_empty()
    }

    /// Get nth element of this sequence.
    ///
    /// If `nth >= self.len()` is satisfied, return `None`.
    pub fn get(&self, nth: usize) -> Option<&M::M> {
        self.seq.get(nth)
    }

    /// Return the range of index of `element`.
    ///
    /// If `element` is not contained by this sequence, return `None`.
    pub fn indexes_of(&self, element: &M::M) -> Option<Range<usize>> {
        let start = self.first_index_of(element)?;
        let end = self
            .upper_bound_node(element)
            .map(|n| n.left().map(|l| l.data.size).unwrap_or(self.len()))?;
        Some(start..end)
    }

    /// Return the smallest index of `element`.
    ///
    /// If `element` is not contained by this sequence, return `None`.
    pub fn first_index_of(&self, element: &M::M) -> Option<usize> {
        Some(
            self.lower_bound_node(element)
                .filter(|n| &n.data.val == element)?
                .left()
                .map(|l| l.data.size)
                .unwrap_or(0),
        )
    }

    /// Return the largest index of `element`.
    ///
    /// If `element` is not contained by this sequence, return `None`.
    pub fn last_index_of(&self, element: &M::M) -> Option<usize> {
        self.indexes_of(element).map(|range| range.end - 1)
    }

    /// Check if `element` is contained by this sequence.
    pub fn contains(&self, element: &M::M) -> bool {
        self.first_index_of(element).is_some()
    }

    /// Split and Return the partition after the `at`th of the sequence.  
    /// The `self` is changed so that the elements after `at` are deleted.
    ///
    /// # Panics
    /// - `at < self.len()` must be satisfied.
    ///
    pub fn split_off(&mut self, at: usize) -> DynamicSortedSequence<M> {
        let seq = self.seq.split_off(at);
        Self { seq }
    }

    /// Search the first node satisfies `element <= node.data.val`.  
    /// In other words,
    /// - if multiple nodes satisfies `element == node.data.val`, return the first of such nodes,
    /// - if such nodes do not exist, return the first node with data that is greater than `element`.
    ///
    /// If such node is found, return `Some` after make it the root of `self`.
    fn lower_bound_node(&self, element: &M::M) -> Option<NodeRef<DSData<M>>> {
        let mut node = self.seq.root.get()?;
        let mut ok = None::<NodeRef<DSData<M>>>;
        loop {
            node.propagate();
            if &node.data.val < element {
                if let Some(right) = node.right() {
                    node = right;
                } else {
                    let res = ok?;
                    res.splay();
                    self.seq.root.set(Some(res));
                    break ok;
                }
            } else {
                ok = Some(node);
                if let Some(left) = node.left() {
                    node = left;
                } else {
                    node.splay();
                    self.seq.root.set(Some(node));
                    break Some(node);
                }
            }
        }
    }

    /// Search the first node satisfies `element < node.data.val`.  
    ///
    /// If such node is found, return `Some` after make it the root of `self`.
    fn upper_bound_node(&self, element: &M::M) -> Option<NodeRef<DSData<M>>> {
        let mut node = self.seq.root.get()?;
        let mut ok = None::<NodeRef<DSData<M>>>;
        loop {
            node.propagate();
            if &node.data.val <= element {
                if let Some(right) = node.right() {
                    node = right;
                } else {
                    let res = ok?;
                    res.splay();
                    self.seq.root.set(Some(res));
                    break Some(res);
                }
            } else {
                ok = Some(node);
                if let Some(left) = node.left() {
                    node = left;
                } else {
                    node.splay();
                    self.seq.root.set(Some(node));
                    break Some(node);
                }
            }
        }
    }

    /// Split and Return the partition after the first position that `element` occurs.  
    /// The effect of this method is almost equivalent `self.split_off(self.first_index_of(element))`.
    ///
    /// If `element` is not contained by this sequence,
    /// split at the position that `element` should be inserted.
    pub fn split_off_by(&mut self, element: &M::M) -> DynamicSortedSequence<M> {
        let Some(mut root) = self.lower_bound_node(element) else {
            return Self::new();
        };

        let left = root.disconnect_left();
        root.update();
        self.seq.root.set(left);

        Self {
            seq: DynamicSequence {
                root: Cell::new(Some(root)),
                alloc: Rc::clone(&self.seq.alloc),
            },
        }
    }

    /// Insert `element`.
    ///
    /// Even if `element` is already contained,
    /// it is inserted at the one of positions the order of this sequence can be kept.
    ///
    /// If there is more than one position to insert, the position is undefined.
    pub fn insert(&mut self, element: M::M) {
        let mut new = self
            .seq
            .alloc
            .borrow_mut()
            .alloc(DSData::with_value(element));
        if let Some(mut node) = self.lower_bound_node(&new.data.val) {
            if let Some(left) = node.disconnect_left() {
                node.update();
                new.connect_left(left);
            }
            new.connect_right(node);
            new.update();
        } else if let Some(root) = self.seq.root.take() {
            new.connect_left(root);
            new.update();
        }
        self.seq.root.set(Some(new));
    }

    /// Pop the first element of this sequence.
    /// If `self.is_empty()` is `true`, return None.
    pub fn pop_first(&mut self) -> Option<M::M> {
        self.seq.pop_first()
    }

    /// Pop the last element of this sequence.
    /// If `self.is_empty()` is `true`, return None.
    pub fn pop_last(&mut self) -> Option<M::M> {
        self.seq.pop_last()
    }

    /// Return the reference of the first element.
    pub fn first(&self) -> Option<&M::M> {
        self.seq
            .first_node()
            .map(|node| unsafe { &node.0.as_ref().data.val })
    }

    /// Return the reference of the last element.
    pub fn last(&self) -> Option<&M::M> {
        self.seq
            .last_node()
            .map(|node| unsafe { &node.0.as_ref().data.val })
    }

    /// Remove `at`th element from this sequence.
    ///
    /// # Panics
    /// - `at < self.len()` must be satisfied.
    pub fn remove(&mut self, at: usize) -> M::M {
        self.seq.remove(at)
    }

    /// Remove the one of `element`.
    ///
    /// If removal occurs, return `Some`, otherwise return `None`.
    pub fn remove_once(&mut self, element: &M::M) -> Option<M::M> {
        let mut back = self.split_off_by(&element);
        if back.first() != Some(element) {
            self.seq.extend(back.seq);
            return None;
        }

        let res = back.pop_first();
        self.seq.append(back.seq);
        res
    }

    /// Remove all `element`.
    ///
    /// Removed elements are returned as an iterator.
    pub fn remove_all<'a>(&'a mut self, element: &'a M::M) -> impl Iterator<Item = M::M> + 'a {
        std::iter::from_fn(move || self.remove_once(element))
    }

    /// Fold values of the range of subsequence specified by `range`.
    pub fn fold(&self, range: impl RangeBounds<usize>) -> M::M {
        self.seq.fold(range)
    }

    pub fn range(&self, range: impl RangeBounds<M::M>) -> RangeIter<'_, M> {
        RangeIter {
            node: match range.start_bound() {
                Bound::Unbounded => self.seq.first_node(),
                Bound::Excluded(m) => self.upper_bound_node(m),
                Bound::Included(m) => self.lower_bound_node(m),
            },
            end: match range.end_bound() {
                Bound::Unbounded => None,
                Bound::Excluded(m) => self.lower_bound_node(m),
                Bound::Included(m) => self.upper_bound_node(m),
            },
            seq: &self.seq,
        }
    }

    pub fn iter(&self) -> Iter<'_, M> {
        self.seq.iter()
    }
}

impl<M> Clone for DynamicSortedSequence<M>
where
    M: MapMonoid,
    M::M: Clone,
    M::Act: Clone,
{
    fn clone(&self) -> Self {
        Self { seq: self.seq.clone() }
    }
}

impl<M> Extend<M::M> for DynamicSortedSequence<M>
where
    M: MapMonoid,
    M::M: Ord + Clone,
{
    /// # Note
    /// This method is equivalent to `iter.into_iter().for_each(|elem| self.insert(elem))`.  
    /// Therefore, the complexity of this method is `O(NlogM)` (`M` is `self.len()`, `N` is `other.len()`).
    fn extend<T: IntoIterator<Item = M::M>>(&mut self, iter: T) {
        iter.into_iter().for_each(|elem| self.insert(elem));
    }
}

impl<M> Debug for DynamicSortedSequence<M>
where
    M: MapMonoid,
    M::M: Debug + Clone,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("DynamicSortedSequence")
            .field("root", &self.seq.root.get())
            .finish()
    }
}

impl<M> Default for DynamicSortedSequence<M>
where
    M: MapMonoid,
    M::M: Ord + Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<M> FromIterator<M::M> for DynamicSortedSequence<M>
where
    M: MapMonoid,
    M::M: Ord + Clone,
{
    fn from_iter<T: IntoIterator<Item = M::M>>(iter: T) -> Self {
        let mut v = iter.into_iter().collect::<Vec<_>>();
        v.sort_unstable();
        Self { seq: v.into_iter().collect() }
    }
}

impl<M> IntoIterator for DynamicSortedSequence<M>
where
    M: MapMonoid,
    M::M: Clone,
{
    type Item = M::M;
    type IntoIter = IntoIter<M>;
    fn into_iter(self) -> Self::IntoIter {
        self.seq.into_iter()
    }
}

pub struct RangeIter<'a, M: MapMonoid>
where
    M::M: Clone,
{
    node: Option<NodeRef<DSData<M>>>,
    end: Option<NodeRef<DSData<M>>>,
    seq: &'a DynamicSequence<M>,
}

impl<'a, M> Iterator for RangeIter<'a, M>
where
    M: MapMonoid,
    M::M: Clone,
{
    type Item = &'a M::M;
    fn next(&mut self) -> Option<Self::Item> {
        (self.node.map(|n| n.data.index()) != self.end.map(|n| n.data.index()))
            .then(|| {
                let mut node = self.node.take()?;
                if !node.is_root() {
                    node.splay();
                    self.seq.root.set(Some(node));
                }
                let res = unsafe { &node.0.as_ref().data.val };
                if let Some(mut next) = node.right() {
                    node.propagate();
                    next.propagate();
                    while let Some(n) = next.left() {
                        next = n;
                        next.propagate();
                    }
                    node.splay();
                    self.node = Some(next);
                    self.seq.root.set(Some(node));
                }
                Some(res)
            })
            .flatten()
    }
}

impl<'a, M> DoubleEndedIterator for RangeIter<'a, M>
where
    M: MapMonoid,
    M::M: Clone,
{
    fn next_back(&mut self) -> Option<Self::Item> {
        (self.node.map(|n| n.data.index()) != self.end.map(|n| n.data.index()))
            .then(|| {
                if let Some(mut end) = self.end {
                    if !end.is_root() {
                        end.splay();
                    }
                    let res = unsafe { &end.0.as_ref().data.val };
                    if let Some(mut prev) = end.left() {
                        end.propagate();
                        prev.propagate();
                        while let Some(n) = prev.right() {
                            prev = n;
                            prev.propagate();
                        }
                        prev.splay();
                        self.end = Some(prev);
                        self.seq.root.set(Some(prev));
                    }
                    Some(res)
                } else {
                    let end = self.seq.last_node()?;
                    let res = unsafe { &end.0.as_ref().data.val };
                    self.end = Some(end);
                    Some(res)
                }
            })
            .flatten()
    }
}

#[cfg(test)]
mod tests {
    use std::{cmp::Reverse, collections::HashMap};

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

    struct S;
    impl MapMonoid for S {
        type M = String;
        type Act = ();

        fn e() -> Self::M {
            "".to_owned()
        }
        fn op(_: &Self::M, _: &Self::M) -> Self::M {
            "".to_owned()
        }

        fn id() -> Self::Act {}
        fn composite(_: &Self::Act, _: &Self::Act) -> Self::Act {}

        fn map(_: &Self::M, _: &Self::Act) -> Self::M {
            "".to_owned()
        }
    }

    #[test]
    fn node_allocator_test() {
        let mut alloc = NodeAllocator::<DSData<S>>::with_capacity(10);
        for _ in 0..20 {
            let mem = alloc.alloc_uninitialized();
            alloc.dealloc(mem);
            let mem = alloc.alloc(DSData {
                index: 0,
                size: 0,
                val: "".to_owned(),
                sum: "".to_owned(),
                lazy: (),
            });
            alloc.dealloc(mem);
        }
        // drop here
    }

    #[test]
    fn string_element_test() {
        let mut seq = DynamicSequence::<S>::new(0);

        seq.push_last("abc".to_owned());
        seq.push_last("def".to_owned());
        seq.push_last("ghi".to_owned());
        seq.push_last("jkl".to_owned());
        seq.push_last("mno".to_owned());
        seq.push_last("pqr".to_owned());
        seq.push_last("stu".to_owned());

        assert_eq!(seq.pop_first(), Some("abc".to_owned()));
        assert_eq!(seq.pop_last(), Some("stu".to_owned()));
        assert_eq!(seq.remove(1), "ghi".to_owned());
        assert_eq!(seq.remove(2), "mno".to_owned());

        assert_eq!(
            seq.into_iter().collect::<Vec<_>>(),
            vec!["def".to_owned(), "jkl".to_owned(), "pqr".to_owned(),]
        )
    }

    struct T;
    impl MapMonoid for T {
        type Act = ();
        type M = Reverse<usize>;
        fn e() -> Self::M {
            Reverse(0)
        }
        fn op(l: &Self::M, _: &Self::M) -> Self::M {
            *l
        }
        fn id() -> Self::Act {}
        fn composite(_: &Self::Act, _: &Self::Act) -> Self::Act {}
        fn map(m: &Self::M, _: &Self::Act) -> Self::M {
            *m
        }
    }

    // https://atcoder.jp/contests/past202203-open/tasks/past202203_m
    #[test]
    fn sorted_seq_random_test() {
        let mut rng = thread_rng();
        let n = 100;
        let q = 10000;
        let mut p = (0..n).map(|_| rng.gen::<usize>()).collect::<Vec<_>>();

        let mut map = HashMap::new();
        for (i, &p) in p.iter().enumerate() {
            map.insert(p, i);
        }
        let mut seq = p
            .iter()
            .cloned()
            .map(|p| Reverse(p))
            .collect::<DynamicSortedSequence<T>>();
        for _ in 0..q {
            let ty: usize = rng.gen_range(1..=3);

            if ty == 1 {
                let a: usize = rng.gen_range(1..=n);
                let x: usize = rng.gen();
                assert!(seq.remove_once(&Reverse(p[a - 1])).is_some());
                seq.insert(Reverse(x));
                p[a - 1] = x;
                map.insert(x, a - 1);
                assert_eq!(seq.len(), n);
            } else if ty == 2 {
                let a: usize = rng.gen_range(0..n);
                let index = seq.first_index_of(&Reverse(p[a]));
                assert!(index.is_some());
                let index = index.unwrap();
                let mut q = p.clone();
                q.sort_unstable_by_key(|&q| Reverse(q));
                assert_eq!(index, q.iter().position(|&q| q == p[a]).unwrap());
            } else {
                let r: usize = rng.gen_range(0..n);
                let p = seq.get(r);
                assert!(p.is_some());
                let p = p.unwrap().0;
                assert!(map.contains_key(&p));
            }
        }
    }
}
