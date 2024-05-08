use std::fmt::Debug;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

pub(crate) trait NodeData: PartialEq + Sized {
    fn update(&mut self, left: Option<NodeRef<Self>>, right: Option<NodeRef<Self>>);
    fn propagate(&mut self, left: Option<NodeRef<Self>>, right: Option<NodeRef<Self>>);
    fn aggrmove(&mut self, source: NodeRef<Self>);
    fn index(&self) -> usize;
}

// Left children are sallower than self, and right children are deeper than self.
pub(crate) struct Node<D: NodeData> {
    parent: Option<NodeRef<D>>,
    pub(crate) left: Option<NodeRef<D>>,
    pub(crate) right: Option<NodeRef<D>>,
    pub(crate) data: D,
}

impl<D: NodeData> Node<D> {
    pub(crate) fn new(data: D) -> Self {
        Self { parent: None, left: None, right: None, data }
    }

    pub(crate) fn propagate(&mut self) {
        self.data.propagate(self.left, self.right);
    }

    pub(crate) fn update(&mut self) {
        self.data.update(self.left, self.right);
    }
}

impl<D: NodeData> PartialEq for Node<D> {
    fn eq(&self, other: &Self) -> bool {
        self.data == other.data
    }
}

impl<D: NodeData + Debug> Debug for Node<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("data", &self.data)
            .field("parent", &self.parent.map(|p| p.data.index()))
            .field("left", &self.left)
            .field("right", &self.right)
            .finish()
    }
}

pub(crate) struct NodeRef<D: NodeData>(NonNull<Node<D>>);

impl<D: NodeData> NodeRef<D> {
    // pub(crate) fn from_raw(ptr: *mut Node<D>) -> Self {
    //     assert_ne!(ptr, null_mut());
    //     unsafe { Self::from_raw_unchecked(ptr) }
    // }

    pub(crate) unsafe fn from_raw_unchecked(ptr: *mut Node<D>) -> Self {
        NodeRef(NonNull::new_unchecked(ptr))
    }

    pub(crate) fn leak(data: D) -> Self {
        unsafe { NodeRef::from_raw_unchecked(Box::leak(Box::new(Node::new(data)))) }
    }

    pub(crate) fn as_ptr(self) -> *mut Node<D> {
        self.0.as_ptr()
    }

    pub(crate) fn connect_left(mut self, mut child: Self) {
        self.left = Some(child);
        child.parent = Some(self);
    }

    pub(crate) fn connect_right(mut self, mut child: Self) {
        self.right = Some(child);
        child.parent = Some(self);
    }

    pub(crate) fn disconnect_left(mut self) -> Option<Self> {
        let mut left = self.left.take()?;
        left.parent = None;
        Some(left)
    }

    pub(crate) fn disconnect_right(mut self) -> Option<Self> {
        let mut right = self.right.take()?;
        right.parent = None;
        Some(right)
    }

    fn disconnect_parent(mut self) -> Option<Self> {
        let mut parent = self.parent.take()?;
        if parent.left == Some(self) {
            parent.left = None;
        } else if parent.right == Some(self) {
            parent.right = None;
        } else {
            unreachable!("There is not connection between the parent and self.");
        }

        Some(parent)
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
        let Some(mut right) = self.disconnect_right() else {
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

        right.data.aggrmove(self);
        self.update();

        let self_is_shallow = self.is_left_child();
        let par = self.disconnect_parent();
        // connect self to right as left-child
        //      c
        //     / \
        //    a   e
        //   / \
        //  b   d
        right.connect_left(self);

        // If self has a parent, disconnect it
        //        a       c
        //       / \       \
        //      b   d       e
        if let Some(par) = par {
            // and connect it to right as a parent
            //           |
            //    a      c
            //   / \      \
            //  b   d      e
            if self_is_shallow {
                par.connect_left(right);
            } else {
                par.connect_right(right);
            }
        }

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
        let Some(mut left) = self.disconnect_left() else {
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

        left.data.aggrmove(self);
        self.update();

        let self_is_shallow = self.is_left_child();
        let par = self.disconnect_parent();
        // connect self to left as right-child
        //      b
        //     / \
        //    d   a
        //       / \
        //      e   c
        left.connect_right(self);
        // If self has a parent, disconnect it
        //        a       b
        //       / \     /
        //      e   c   d
        if let Some(par) = par {
            // and connect it to left as a parent
            if self_is_shallow {
                par.connect_left(left);
            } else {
                par.connect_right(left);
            }
        }

        // return new root of the original subtree
        left
    }

    /// # Constraint
    /// - The ancestor of `self` should have no action to propagate.
    pub(crate) fn splay(mut self) {
        self.propagate();
        while !self.is_root() {
            let parent = self.parent.unwrap();

            if parent.is_root() {
                // zig step
                if self.is_left_child() {
                    parent.rotate_right();
                } else {
                    parent.rotate_left();
                }
                return;
            }

            let grand_parent = parent.parent.unwrap();
            let sf = self.is_left_child();
            let pf = parent.is_left_child();
            if sf ^ pf {
                // zig-zag step
                if sf {
                    parent.rotate_right();
                    grand_parent.rotate_left();
                } else {
                    parent.rotate_left();
                    grand_parent.rotate_right();
                }
            } else {
                // zig-zig step
                if sf {
                    grand_parent.rotate_right();
                    parent.rotate_right();
                } else {
                    grand_parent.rotate_left();
                    parent.rotate_left();
                }
            }
        }
    }

    fn is_left_child(self) -> bool {
        self.parent.map_or(false, |p| p.left == Some(self))
    }

    pub(crate) fn is_root(self) -> bool {
        self.parent.is_none()
    }
}

impl<D: NodeData> Clone for NodeRef<D> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<D: NodeData> Copy for NodeRef<D> {}

impl<D: NodeData> PartialEq for NodeRef<D> {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl<D: NodeData> Deref for NodeRef<D> {
    type Target = Node<D>;
    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl<D: NodeData> DerefMut for NodeRef<D> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut() }
    }
}

impl<D: NodeData + Debug> Debug for NodeRef<D> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NodeRef")
            .field("data", &self.data)
            .field("parent", &self.parent.map(|p| p.data.index()))
            .field("left", &self.left)
            .field("right", &self.right)
            .finish()
    }
}
