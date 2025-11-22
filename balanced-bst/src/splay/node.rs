use std::ops::{Deref, DerefMut};
use std::{fmt::Debug, ptr::NonNull};

pub(super) struct SplayNode<K, V> {
    pub(super) parent: Option<SplayNodeRef<K, V>>,
    pub(super) left: Option<SplayNodeRef<K, V>>,
    pub(super) right: Option<SplayNodeRef<K, V>>,
    pub(super) key: K,
    pub(super) val: V,
}

impl<K, V> SplayNode<K, V> {
    pub const fn new(key: K, val: V) -> Self {
        Self { parent: None, left: None, right: None, key, val }
    }
}

impl<K: Ord, V> PartialEq for SplayNode<K, V> {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl<K: Ord, V> PartialOrd for SplayNode<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        self.key.partial_cmp(&other.key)
    }
}

impl<K: Debug, V: Debug> Debug for SplayNode<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SplayNode")
            .field("key", &self.key)
            .field("val", &self.val)
            .field("left", &self.left.map(|n| unsafe { n.0.as_ref() }))
            .field("right", &self.right.map(|n| unsafe { n.0.as_ref() }))
            .finish()
    }
}

pub(super) struct SplayNodeRef<K, V>(pub(super) NonNull<SplayNode<K, V>>);

impl<K: Ord + Debug, V: Debug> SplayNodeRef<K, V> {
    pub(super) fn new(node: SplayNode<K, V>) -> Self {
        let reference = Box::leak(Box::new(node));
        Self(NonNull::new(reference as *mut _).unwrap())
    }

    /// # Safety
    /// * This function must be called **ONLY ONCE**.
    /// * Since this function call, the Node<T> referenced by NodeRef<T> will be dropped and may return values that are not normal.
    pub(super) unsafe fn into_raw(self) -> SplayNode<K, V> {
        let bx = Box::from_raw(self.0.as_ptr());
        *bx
    }

    pub(super) fn connect_left(mut self, mut child: Self) {
        assert_ne!(self.key, child.key);
        self.left = Some(child);
        child.parent = Some(self);
    }

    pub(super) fn connect_right(mut self, mut child: Self) {
        assert_ne!(self.key, child.key);
        self.right = Some(child);
        child.parent = Some(self);
    }

    pub(super) fn connect_child(self, child: Self) -> Result<(), &'static str> {
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

    pub(super) fn disconnect_left(mut self) -> Option<Self> {
        if let Some(mut left) = self.left {
            left.parent = None;
            self.left = None;
            Some(left)
        } else {
            None
        }
    }

    pub(super) fn disconnect_right(mut self) -> Option<Self> {
        if let Some(mut right) = self.right {
            right.parent = None;
            self.right = None;
            Some(right)
        } else {
            None
        }
    }

    pub(super) fn disconnect_parent(&mut self) -> Option<Self> {
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
    pub(super) fn rotate_left(mut self) -> Self {
        // If self has right-child, disconnect it.
        //      |
        //      a
        //     /
        //    b   c
        //       / \
        //      d   e
        // If not, it is not necessary to do anything.
        let Some(right) = self.disconnect_right() else {
            return self;
        };

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
    pub(super) fn rotate_right(mut self) -> Self {
        // If self has left-child, disconnect it.
        //      |
        //      a
        //       \
        //    b   c
        //   / \
        //  d   e
        // If not, it is not necessary to do anything.
        let Some(left) = self.disconnect_left() else {
            return self;
        };

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

    pub(super) fn splay(mut self, key: &K) -> Self {
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

    pub(super) fn is_left_child(self) -> bool {
        self.parent
            .is_some_and(|p| p.left.is_some_and(|l| l.key == self.key))
    }

    pub(super) fn is_right_child(self) -> bool {
        self.parent
            .is_some_and(|p| p.right.is_some_and(|r| r.key == self.key))
    }
}

impl<K, V> Clone for SplayNodeRef<K, V> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<K, V> Copy for SplayNodeRef<K, V> {}

impl<K: Ord, V> PartialEq for SplayNodeRef<K, V> {
    fn eq(&self, other: &Self) -> bool {
        unsafe { self.0.as_ref() == other.0.as_ref() }
    }
}

impl<K: Ord, V> PartialOrd for SplayNodeRef<K, V> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        unsafe { self.0.as_ref().partial_cmp(other.0.as_ref()) }
    }
}

impl<K, V> Deref for SplayNodeRef<K, V> {
    type Target = SplayNode<K, V>;
    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl<K, V> DerefMut for SplayNodeRef<K, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut() }
    }
}

impl<K: Debug, V: Debug> Debug for SplayNodeRef<K, V> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("SplayNodeRef")
            .field("key", &self.key)
            .field("val", &self.val)
            .field("left", &self.left.map(|n| unsafe { n.0.as_ref() }))
            .field("right", &self.right.map(|n| unsafe { n.0.as_ref() }))
            .finish()
    }
}
