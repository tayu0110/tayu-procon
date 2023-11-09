use std::iter::FusedIterator;
use std::marker::PhantomData;
use std::ops::{Bound, Deref, DerefMut, RangeBounds};
use std::{cell::Cell, fmt::Debug, ptr::NonNull};

struct SplayNode<K, V> {
    parent: Option<SplayNodeRef<K, V>>,
    left: Option<SplayNodeRef<K, V>>,
    right: Option<SplayNodeRef<K, V>>,
    key: K,
    val: V,
}

impl<K, V> SplayNode<K, V> {
    pub const fn new(key: K, val: V) -> Self {
        Self { parent: None, left: None, right: None, key, val }
    }
}

impl<K: Ord, V> PartialEq for SplayNode<K, V> {
    fn eq(&self, other: &Self) -> bool { self.key == other.key }
}

impl<K: Ord, V> PartialOrd for SplayNode<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.key.partial_cmp(&other.key)
    }
}

impl<K: Debug, V: Debug> Debug for SplayNode<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "SplayNode {{ left: {:?}, right: {:?}, key: {:?} val: {:?} }}",
            self.left.map(|n| unsafe { n.0.as_ref() }),
            self.right.map(|n| unsafe { n.0.as_ref() }),
            self.key,
            self.val
        )
    }
}

struct SplayNodeRef<K, V>(NonNull<SplayNode<K, V>>);

impl<K: Ord + Debug, V: Debug> SplayNodeRef<K, V> {
    fn new(node: SplayNode<K, V>) -> Self {
        let reference = Box::leak(Box::new(node));
        Self(NonNull::new(reference as *mut _).unwrap())
    }

    /// # Safety
    /// * This function must be called **ONLY ONCE**.
    /// * Since this function call, the Node<T> referenced by NodeRef<T> will be dropped and may return values that are not normal.
    unsafe fn into_raw(self) -> SplayNode<K, V> {
        let bx = Box::from_raw(self.0.as_ptr());
        *bx
    }

    fn connect_left(mut self, mut child: Self) {
        assert_ne!(self.key, child.key);
        self.left = Some(child);
        child.parent = Some(self);
    }

    fn connect_right(mut self, mut child: Self) {
        assert_ne!(self.key, child.key);
        self.right = Some(child);
        child.parent = Some(self);
    }

    pub fn connect_child(self, child: Self) -> Result<(), &'static str> {
        assert_ne!(self.key, child.key);

        if self.key > child.key {
            if self.left.is_some() {
                return Err("Left child already exists.");
            }
            self.connect_left(child);
        } else if self.key < child.key {
            if self.right.is_some() {
                return Err("Right child is already exists");
            }
            self.connect_right(child);
        } else {
            return Err("Duplicate Node");
        }

        Ok(())
    }

    fn disconnect_left(mut self) -> Option<Self> {
        if let Some(mut left) = self.left {
            left.parent = None;
            self.left = None;
            Some(left)
        } else {
            None
        }
    }

    fn disconnect_right(mut self) -> Option<Self> {
        if let Some(mut right) = self.right {
            right.parent = None;
            self.right = None;
            Some(right)
        } else {
            None
        }
    }

    fn disconnect_parent(&mut self) -> Option<Self> {
        if let Some(mut parent) = self.parent {
            match (parent.left, parent.right) {
                (Some(l), _) if l.key == self.key => {
                    assert!(self.key < parent.key);
                    parent.left = None;
                    self.parent = None;
                }
                (_, Some(r)) if r.key == self.key => {
                    assert!(self.key > parent.key);
                    parent.right = None;
                    self.parent = None;
                }
                _ => {
                    unreachable!()
                }
            }

            Some(parent)
        } else {
            None
        }
    }

    /// Rotate the subtree whose root is `target` to the left and return new root of this subtree.
    /// Specifically, it is equivalent to the following pseudo code
    ///
    /// `right = self.right_child`  <br/>
    /// `target.right_child = right.left_child` <br/>
    /// `right.left_child = target`
    //           |                  |
    //           a                  c
    //          / \                / \
    //         b   c      ->      a   e
    //            / \            / \
    //           d   e          b   d
    fn rotate_left(mut self) -> Self {
        // If self has right-child, disconnect it.
        //      |
        //      a
        //     /
        //    b   c
        //       / \
        //      d   e
        // If not, it is not necessary to do anything.
        let Some(right) = self.disconnect_right() else { return self };

        // If right has left-child, disconnect it
        //      |
        //      a
        //     /
        //    b   c
        //         \
        //      d   e
        if let Some(right_left) = right.disconnect_left() {
            // and connect to self as right-child
            //     |
            //     a     c
            //    / \     \
            //   b   d     e
            self.connect_right(right_left);
        }

        // If self has a parent, disconnect it
        //        a       c
        //       / \       \
        //      b   d       e
        if let Some(par) = self.disconnect_parent() {
            // and connect it to right as a parent
            //           |
            //    a      c
            //   / \      \
            //  b   d      e
            par.connect_child(right).unwrap();
        }

        // connect self to right as left-child
        //      |
        //      c
        //     / \
        //    a   e
        //   / \
        //  b   d
        right.connect_left(self);

        // return new root of the original subtree.
        right
    }

    /// Rotate the subtree whose root is `target` to the right and return new root of this subtree.
    /// Specifically, it is equivalent to the following pseudo code
    ///
    /// `left = self.left_child`  <br/>
    /// `target.left_child = left.right_child` <br/>
    /// `left.right_child = target`
    //         |              |
    //         a              b
    //        / \            / \
    //       b   c   ->     d   a
    //      / \                / \
    //     d   e              e   c
    fn rotate_right(mut self) -> Self {
        // If self has left-child, disconnect it.
        //      |
        //      a
        //       \
        //    b   c
        //   / \
        //  d   e
        // If not, it is not necessary to do anything.
        let Some(left) = self.disconnect_left() else { return self };

        // If left has right-child, disconnect it
        //      |
        //      a
        //       \
        //    b   c
        //   /
        //  d   e
        if let Some(left_right) = left.disconnect_right() {
            // and connect it to self as left-child
            //     |
            //     a         b
            //    / \       /
            //   e   c     d
            self.connect_left(left_right);
        }

        // If self has a parent, disconnect it
        //        a       b
        //       / \     /
        //      e   c   d
        if let Some(par) = self.disconnect_parent() {
            // and connect it to left as a parent
            par.connect_child(left).unwrap();
        }

        // connect self to left as right-child
        //      |
        //      b
        //     / \
        //    d   a
        //       / \
        //      e   c
        left.connect_right(self);

        // return new root of the original subtree
        left
    }

    fn splay(mut self, key: &K) -> Self {
        // If found the target node, return it.
        if &self.key == key {
            return self;
        }

        if key < &self.key {
            let Some(left) = self.left else { return self };

            if key < &left.key {
                if let Some(left_left) = left.disconnect_left() {
                    let left_left = left_left.splay(key);
                    left.connect_left(left_left);
                }

                self = self.rotate_right();
            } else if key > &left.key {
                if let Some(left_right) = left.disconnect_right() {
                    let left_right = left_right.splay(key);
                    left.connect_right(left_right);
                }

                left.rotate_left();
            }

            self.rotate_right()
        } else {
            let Some(right) = self.right else { return self };

            if key < &right.key {
                if let Some(right_left) = right.disconnect_left() {
                    let right_left = right_left.splay(key);
                    right.connect_left(right_left);
                }

                right.rotate_right();
            } else if key > &right.key {
                if let Some(right_right) = right.disconnect_right() {
                    let right_right = right_right.splay(key);
                    right.connect_right(right_right);
                }

                self = self.rotate_left();
            }

            self.rotate_left()
        }
    }

    fn is_left_child(self) -> bool {
        self.parent
            .map_or(false, |p| p.left.map_or(false, |l| l.key == self.key))
    }

    fn is_right_child(self) -> bool {
        self.parent
            .map_or(false, |p| p.right.map_or(false, |r| r.key == self.key))
    }
}

impl<K, V> Clone for SplayNodeRef<K, V> {
    fn clone(&self) -> Self { Self(self.0) }
}

impl<K, V> Copy for SplayNodeRef<K, V> {}

impl<K: Ord, V> PartialEq for SplayNodeRef<K, V> {
    fn eq(&self, other: &Self) -> bool { unsafe { self.0.as_ref() == other.0.as_ref() } }
}

impl<K: Ord, V> PartialOrd for SplayNodeRef<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        unsafe { self.0.as_ref().partial_cmp(other.0.as_ref()) }
    }
}

impl<K, V> Deref for SplayNodeRef<K, V> {
    type Target = SplayNode<K, V>;
    fn deref(&self) -> &Self::Target { unsafe { self.0.as_ref() } }
}

impl<K, V> DerefMut for SplayNodeRef<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { self.0.as_mut() } }
}

impl<K: Debug, V: Debug> Debug for SplayNodeRef<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "SplayNodeRef {{ key: {:?}, val: {:?}, left: {:?}, right: {:?} }}",
            self.key,
            self.val,
            self.left.map(|n| unsafe { n.0.as_ref() }),
            self.right.map(|n| unsafe { n.0.as_ref() }),
        )
    }
}

#[derive(Debug)]
pub struct SplayTreeMap<K, V> {
    len: usize,
    root: Option<Cell<SplayNodeRef<K, V>>>,
}

impl<K: Ord + Debug, V: Debug> SplayTreeMap<K, V> {
    pub const fn new() -> Self { Self { len: 0, root: None } }

    pub const fn len(&self) -> usize { self.len }

    pub const fn is_empty(&self) -> bool { self.len() == 0 }

    pub fn contains_key(&self, key: &K) -> bool { self.get(key).is_some() }

    pub fn get(&self, key: &K) -> Option<&V> {
        let root = self.root.as_ref()?;

        let res = root.get().splay(key);
        assert!(res.parent.is_none());
        root.replace(res);

        unsafe { (&res.key == key).then_some(&res.0.as_ref().val) }
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let root = self.root.as_ref()?;

        let mut res = root.get().splay(key);
        assert!(res.parent.is_none());
        root.replace(res);

        unsafe { (&res.key == key).then_some(&mut res.0.as_mut().val) }
    }

    pub fn insert(&mut self, key: K, val: V) {
        let Some(root) = self.root.as_ref() else {
            self.root = Some(Cell::new(SplayNodeRef::new(SplayNode::new(key, val))));
            self.len += 1;
            return;
        };

        let mut node = root.get().splay(&key);
        assert!(node.parent.is_none());
        root.replace(node);

        if node.key == key {
            node.val = val;
            return;
        }

        self.len += 1;
        loop {
            if key < node.key {
                if let Some(left) = node.left {
                    node = left;
                } else {
                    node.connect_left(SplayNodeRef::new(SplayNode::new(key, val)));
                    return;
                }
            } else {
                if let Some(right) = node.right {
                    node = right;
                } else {
                    node.connect_right(SplayNodeRef::new(SplayNode::new(key, val)));
                    return;
                }
            }
        }
    }

    pub fn remove(&mut self, key: &K) -> Option<V> {
        let root = self.root.as_ref()?;

        let node = root.get().splay(key);
        assert!(node.parent.is_none());

        if &node.key != key {
            root.replace(node);
            return None;
        }

        self.len -= 1;
        match (node.disconnect_left(), node.disconnect_right()) {
            (Some(left), Some(right)) => {
                if let Some(mut right_most_left) = right.left {
                    while let Some(l) = right_most_left.left {
                        right_most_left = l;
                    }
                    let p = right_most_left.disconnect_parent().unwrap();
                    if let Some(r) = right_most_left.disconnect_right() {
                        p.connect_left(r);
                    }

                    right_most_left.connect_left(left);
                    right_most_left.connect_right(right);
                    root.replace(right_most_left);
                } else {
                    right.connect_left(left);
                    root.replace(right);
                }
            }
            (Some(c), None) | (None, Some(c)) => {
                root.replace(c);
            }
            (None, None) => {
                self.root = None;
            }
        }

        let res = unsafe { node.into_raw() };
        Some(res.val)
    }

    pub fn first_key_value(&self) -> Option<(&K, &V)> {
        let mut node = self.root.as_ref()?.get();

        while let Some(left) = node.left {
            node = left;
        }

        unsafe {
            let r = node.0.as_ref();
            Some((&r.key, &r.val))
        }
    }

    pub fn last_key_value(&self) -> Option<(&K, &V)> {
        let mut node = self.root.as_ref()?.get();

        while let Some(right) = node.right {
            node = right;
        }

        unsafe {
            let r = node.0.as_ref();
            Some((&r.key, &r.val))
        }
    }

    pub fn iter(&self) -> Iter<K, V> {
        Iter {
            front: self.root.as_ref().map(|c| {
                let mut node = c.get();
                while let Some(left) = node.left {
                    node = left;
                }
                node
            }),
            back: self.root.as_ref().map(|c| {
                let mut node = c.get();
                while let Some(right) = node.right {
                    node = right;
                }
                node
            }),
            _phantom: PhantomData,
        }
    }

    pub fn range(&self, range: impl RangeBounds<K>) -> Range<K, V> {
        Range {
            iter: Iter {
                front: self.root.as_ref().and_then(|c| {
                    let mut node = c.get();
                    let mut keep = None;
                    loop {
                        if range.contains(&node.key) {
                            keep = Some(node);
                            match node.left {
                                Some(left) => {
                                    node = left;
                                }
                                _ => break keep,
                            }
                        } else {
                            match (range.start_bound(), range.end_bound()) {
                                (Bound::Included(s), _) if &node.key < s => {
                                    let Some(right) = node.right else { break keep };
                                    node = right;
                                }
                                (Bound::Excluded(s), _) if &node.key <= s => {
                                    let Some(right) = node.right else { break keep };
                                    node = right;
                                }
                                (_, Bound::Included(s)) if s < &node.key => {
                                    let Some(left) = node.left else { break keep };
                                    node = left;
                                }
                                (_, Bound::Excluded(s)) if s <= &node.key => {
                                    let Some(left) = node.left else { break keep };
                                    node = left;
                                }
                                _ => break keep,
                            }
                        }
                    }
                }),
                back: self.root.as_ref().and_then(|c| {
                    let mut node = c.get();
                    let mut keep = None;
                    loop {
                        if range.contains(&node.key) {
                            keep = Some(node);
                            match node.right {
                                Some(right) => {
                                    node = right;
                                }
                                _ => break keep,
                            }
                        } else {
                            match (range.start_bound(), range.end_bound()) {
                                (Bound::Included(s), _) if &node.key < s => {
                                    let Some(right) = node.right else { break keep };
                                    node = right;
                                }
                                (Bound::Excluded(s), _) if &node.key <= s => {
                                    let Some(right) = node.right else { break keep };
                                    node = right;
                                }
                                (_, Bound::Included(s)) if s < &node.key => {
                                    let Some(left) = node.left else { break keep };
                                    node = left;
                                }
                                (_, Bound::Excluded(s)) if s <= &node.key => {
                                    let Some(left) = node.left else { break keep };
                                    node = left;
                                }
                                _ => break keep,
                            }
                        }
                    }
                }),
                _phantom: PhantomData,
            },
        }
    }
}

// This represents a range `front..=back`.
// `front` and `back` is inclusive.
pub struct Iter<'a, K, V> {
    front: Option<SplayNodeRef<K, V>>,
    back: Option<SplayNodeRef<K, V>>,
    _phantom: PhantomData<&'a (K, V)>,
}

impl<'a, K: Ord + Debug, V: Debug> Iterator for Iter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        let mut node = self.front?;

        let res = unsafe { (&node.0.as_ref().key, &node.0.as_ref().val) };

        (self.front <= self.back).then(|| {
            if let Some(mut nt) = node.right {
                while let Some(left) = nt.left {
                    nt = left;
                }

                self.front = Some(nt);
            } else {
                while node.is_right_child() {
                    let Some(par) = node.parent else { break };
                    node = par;
                }

                self.front = node.parent;
            }

            res
        })
    }
}

impl<'a, K: Ord + Debug, V: Debug> DoubleEndedIterator for Iter<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> {
        let mut node = self.back?;

        (self.front.is_some() && self.front <= self.back).then(|| {
            let res = unsafe { (&node.0.as_ref().key, &node.0.as_ref().val) };

            if let Some(mut nt) = node.left {
                while let Some(right) = nt.right {
                    nt = right;
                }

                self.back = Some(nt);
            } else {
                while node.is_left_child() {
                    let Some(par) = node.parent else { break };
                    node = par;
                }

                self.back = node.parent;
            }

            res
        })
    }
}

impl<'a, K: Ord + Debug, V: Debug> FusedIterator for Iter<'a, K, V> {}

pub struct Range<'a, K, V> {
    iter: Iter<'a, K, V>,
}

impl<'a, K: Ord + Debug, V: Debug> Iterator for Range<'a, K, V> {
    type Item = <Iter<'a, K, V> as Iterator>::Item;

    fn next(&mut self) -> Option<Self::Item> { self.iter.next() }
}

impl<'a, K: Ord + Debug, V: Debug> DoubleEndedIterator for Range<'a, K, V> {
    fn next_back(&mut self) -> Option<Self::Item> { self.iter.next_back() }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rand::{thread_rng, Rng};

    #[test]
    fn add_child_test() {
        let a = SplayNodeRef::new(SplayNode::new(10u32, 10u32));
        let b = SplayNodeRef::new(SplayNode::new(20u32, 20u32));
        let c = SplayNodeRef::new(SplayNode::new(30u32, 30u32));

        // make tree as the following
        //      a
        //     / \
        //    b   c
        a.connect_left(b);
        a.connect_right(c);

        assert_eq!(a.left, Some(b));
        assert_eq!(a.right, Some(c));
        assert_eq!(b.parent, Some(a));
        assert_eq!(c.parent, Some(a));
    }

    #[test]
    fn rotate_left_test() {
        let a = SplayNodeRef::new(SplayNode::new(20u32, 20u32));
        let b = SplayNodeRef::new(SplayNode::new(10u32, 10u32));
        let c = SplayNodeRef::new(SplayNode::new(40u32, 40u32));
        let d = SplayNodeRef::new(SplayNode::new(30u32, 30u32));
        let e = SplayNodeRef::new(SplayNode::new(50u32, 50u32));

        // make tree as the following
        //      a
        //     / \
        //    b   c
        //       / \
        //      d   e
        a.connect_left(b);
        a.connect_right(c);
        c.connect_left(d);
        c.connect_right(e);

        // rotate left at node 'a'
        //      c
        //     / \
        //    a   e
        //   / \
        //  b   d
        a.rotate_left();
        assert_eq!(a.parent, Some(c));
        assert_eq!(a.left, Some(b));
        assert_eq!(a.right, Some(d));
        assert_eq!(b.parent, Some(a));
        assert_eq!(b.left, None);
        assert_eq!(b.right, None);
        assert_eq!(c.parent, None);
        assert_eq!(c.left, Some(a));
        assert_eq!(c.right, Some(e));
        assert_eq!(d.parent, Some(a));
        assert_eq!(d.left, None);
        assert_eq!(d.right, None);
        assert_eq!(e.parent, Some(c));
        assert_eq!(e.left, None);
        assert_eq!(e.right, None);

        // rotate left at node 'a' again
        //       c
        //      / \
        //     d   e
        //    /
        //   a
        //  /
        // b
        a.rotate_left();
        assert_eq!(a.parent, Some(d));
        assert_eq!(a.left, Some(b));
        assert_eq!(a.right, None);
        assert_eq!(b.parent, Some(a));
        assert_eq!(b.left, None);
        assert_eq!(b.right, None);
        assert_eq!(c.parent, None);
        assert_eq!(c.left, Some(d));
        assert_eq!(c.right, Some(e));
        assert_eq!(d.parent, Some(c));
        assert_eq!(d.left, Some(a));
        assert_eq!(d.right, None);
        assert_eq!(e.parent, Some(c));
        assert_eq!(e.left, None);
        assert_eq!(e.right, None);
    }

    #[test]
    fn rotate_right_test() {
        let a = SplayNodeRef::new(SplayNode::new(40u32, 40u32));
        let b = SplayNodeRef::new(SplayNode::new(20u32, 20u32));
        let c = SplayNodeRef::new(SplayNode::new(50u32, 50u32));
        let d = SplayNodeRef::new(SplayNode::new(10u32, 10u32));
        let e = SplayNodeRef::new(SplayNode::new(30u32, 30u32));

        // make tree as the following
        //      a
        //     / \
        //    b   c
        //   / \
        //  d   e
        a.connect_left(b);
        a.connect_right(c);
        b.connect_left(d);
        b.connect_right(e);

        // rotate right at node 'a'
        //      b
        //     / \
        //    d   a
        //       / \
        //      e   c
        a.rotate_right();
        assert_eq!(a.parent, Some(b));
        assert_eq!(a.left, Some(e));
        assert_eq!(a.right, Some(c));
        assert_eq!(b.parent, None);
        assert_eq!(b.left, Some(d));
        assert_eq!(b.right, Some(a));
        assert_eq!(c.parent, Some(a));
        assert_eq!(c.left, None);
        assert_eq!(c.right, None);
        assert_eq!(d.parent, Some(b));
        assert_eq!(d.left, None);
        assert_eq!(d.right, None);
        assert_eq!(e.parent, Some(a));
        assert_eq!(e.left, None);
        assert_eq!(e.right, None);

        // rotate right at node 'a' again
        //     b
        //    / \
        //   d   e
        //        \
        //         a
        //          \
        //           c
        a.rotate_right();
        assert_eq!(a.parent, Some(e));
        assert_eq!(a.left, None);
        assert_eq!(a.right, Some(c));
        assert_eq!(b.parent, None);
        assert_eq!(b.left, Some(d));
        assert_eq!(b.right, Some(e));
        assert_eq!(c.parent, Some(a));
        assert_eq!(c.left, None);
        assert_eq!(c.right, None);
        assert_eq!(d.parent, Some(b));
        assert_eq!(d.left, None);
        assert_eq!(d.right, None);
        assert_eq!(e.parent, Some(b));
        assert_eq!(e.left, None);
        assert_eq!(e.right, Some(a));
    }

    // This function is a helper function.
    // `test` attribute is not necessary.
    fn bst_constraint_test(node: SplayNodeRef<i32, i32>, min: i32, max: i32) -> bool {
        let mut res = true;

        if let Some(left) = node.left {
            if min < left.key && left.key < node.key.min(max) {
                res &= bst_constraint_test(left, min, node.key.min(max));
            } else {
                return false;
            }
        }

        if let Some(right) = node.right {
            if node.key.max(min) < right.key && right.key < max {
                res &= bst_constraint_test(right, node.key.max(min), max);
            } else {
                return false;
            }
        }

        res
    }

    #[test]
    fn splay_test() {
        let a = SplayNodeRef::new(SplayNode::new(40, 40));
        let b = SplayNodeRef::new(SplayNode::new(20, 20));
        let c = SplayNodeRef::new(SplayNode::new(50, 50));
        let d = SplayNodeRef::new(SplayNode::new(10, 10));
        let e = SplayNodeRef::new(SplayNode::new(30, 30));

        a.connect_left(b);
        a.connect_right(c);
        b.connect_left(d);
        b.connect_right(e);

        let root = a.splay(&10);
        eprintln!("root: {root:?}");
        assert_eq!(root.parent, None);
        assert_eq!(root.val, 10);
        assert!(bst_constraint_test(root, i32::MIN, i32::MAX));

        let root = root.splay(&60);
        eprintln!("root: {root:?}");
        assert_eq!(root.parent, None);
        assert_ne!(root.val, 60);
        assert!(bst_constraint_test(root, i32::MIN, i32::MAX));

        let root = root.splay(&40);
        eprintln!("root: {root:?}");
        assert_eq!(root.parent, None);
        assert_eq!(root.val, 40);
        assert!(bst_constraint_test(root, i32::MIN, i32::MAX));

        let root = root.splay(&20);
        eprintln!("root: {root:?}");
        assert_eq!(root.parent, None);
        assert_eq!(root.val, 20);
        assert!(bst_constraint_test(root, i32::MIN, i32::MAX));
    }

    #[test]
    fn splay_tree_test() {
        let mut tree = SplayTreeMap::new();
        tree.insert(10, 10);
        tree.insert(20, 20);

        assert_eq!(tree.get(&10).unwrap(), &10);
        assert_eq!(tree.len(), 2);

        tree.insert(10, 15);
        assert_eq!(tree.get(&10).unwrap(), &15);
        assert_eq!(tree.len(), 2);

        tree.remove(&10);
        assert_eq!(tree.len(), 1);

        tree.remove(&10);
        assert_eq!(tree.len(), 1);

        tree.remove(&20);
        assert!(tree.is_empty());
    }

    #[test]
    fn iterator_test() {
        let mut tree = SplayTreeMap::new();
        let mut expected = vec![];
        let mut rng = thread_rng();

        while expected.len() < 20 {
            let (k, v): (u32, u32) = (rng.gen_range(0..50), rng.gen_range(0..50));
            if !tree.contains_key(&k) {
                tree.insert(k, v);
                expected.push((k, v));
            }
        }

        expected.sort();

        let v = tree.iter().map(|(&k, &v)| (k, v)).collect::<Vec<_>>();
        assert_eq!(v, expected);

        let v = tree
            .iter()
            .skip(2)
            .take(3)
            .map(|(&k, &v)| (k, v))
            .collect::<Vec<_>>();
        assert_eq!(&v, &expected[2..5]);

        let v = tree
            .range(2..=10)
            .map(|(&k, &v)| (k, v))
            .collect::<Vec<_>>();
        assert_eq!(
            v,
            expected
                .iter()
                .cloned()
                .filter(|v| (2..=10).contains(&v.0))
                .collect::<Vec<_>>()
        );

        expected.reverse();

        let v = tree.iter().rev().map(|(&k, &v)| (k, v)).collect::<Vec<_>>();
        assert_eq!(v, expected);
    }
}
