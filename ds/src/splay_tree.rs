use std::fmt::Debug;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

pub(crate) trait NodeData: PartialEq + Sized {
    fn update(&mut self, left: Option<NodeRef<Self>>, right: Option<NodeRef<Self>>);
    fn propagate(&mut self, left: Option<NodeRef<Self>>, right: Option<NodeRef<Self>>);
    fn aggrmove(&mut self, source: NodeRef<Self>);
    fn toggle(&mut self) {}
    fn index(&self) -> usize;
}

// Left children are sallower than self, and right children are deeper than self.
pub(crate) struct Node<D: NodeData> {
    parent: Option<NodeRef<D>>,
    // 0: left, 1: right
    child: [Option<NodeRef<D>>; 2],
    pub(crate) data: D,
}

impl<D: NodeData> Node<D> {
    pub(crate) fn new(data: D) -> Self {
        Self { parent: None, child: [None; 2], data }
    }

    pub(crate) fn initialize(&mut self, data: D) {
        self.parent = None;
        self.child = [None; 2];
        self.data = data;
    }

    pub(crate) fn propagate(&mut self) {
        self.data.propagate(self.left(), self.right());
    }

    pub(crate) fn update(&mut self) {
        self.data.update(self.left(), self.right());
    }

    pub(crate) fn toggle(&mut self) {
        self.data.toggle();
        self.child.swap(0, 1);
    }

    pub(crate) const fn left(&self) -> Option<NodeRef<D>> {
        self.child[0]
    }

    pub(crate) const fn right(&self) -> Option<NodeRef<D>> {
        self.child[1]
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
            .field("left", &self.left())
            .field("right", &self.right())
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

    // pub(crate) fn leak(data: D) -> Self {
    //     unsafe { NodeRef::from_raw_unchecked(Box::leak(Box::new(Node::new(data)))) }
    // }

    // pub(crate) fn as_ptr(self) -> *mut Node<D> {
    //     self.0.as_ptr()
    // }

    fn connect(mut self, mut child: Self, right: bool) {
        self.child[right as usize] = Some(child);
        child.parent = Some(self);
    }

    pub(crate) fn connect_left(self, child: Self) {
        self.connect(child, false);
    }

    pub(crate) fn connect_right(self, child: Self) {
        self.connect(child, true);
    }

    fn disconnect(mut self, right: bool) -> Option<Self> {
        let mut child = self.child[right as usize].take()?;
        child.parent = None;
        Some(child)
    }

    pub(crate) fn disconnect_left(self) -> Option<Self> {
        self.disconnect(false)
    }

    pub(crate) fn disconnect_right(self) -> Option<Self> {
        self.disconnect(true)
    }

    // Returned boolean value is `is self right child`
    fn disconnect_parent(mut self) -> Option<(Self, bool)> {
        let mut parent = self.parent.take()?;
        let is_right_child = parent.child[0] != Some(self);
        parent.child[is_right_child as usize] = None;
        Some((parent, is_right_child))
    }

    fn rotate(mut self, right: bool) -> Self {
        // The following comments are made when `right` is `true`.
        // When `right` is `false`, left and right are reversed.
        let left = !right;
        // If self has left-child, disconnect it.
        //      |
        //      a
        //       \
        //    b   c
        //   / \
        //  d   e
        // If not, it is not necessary to do anything.
        let Some(mut child) = self.disconnect(left) else {
            return self;
        };

        // If left has right-child, disconnect it
        //      |
        //      a
        //       \
        //    b   c
        //   /
        //  d   e
        if let Some(grand_child) = child.disconnect(right) {
            // and connect it to self as left-child
            //     |
            //     a         b
            //    / \       /
            //   e   c     d
            self.connect(grand_child, left);
        }

        child.data.aggrmove(self);
        self.update();

        // If self has a parent, disconnect it
        //        a       b
        //       / \     /
        //      e   c   d
        if let Some((par, is_right_child)) = self.disconnect_parent() {
            // and connect it to left as a parent
            par.connect(child, is_right_child);
        }
        // connect self to left as right-child
        //      b
        //     / \
        //    d   a
        //       / \
        //      e   c
        child.connect(self, right);

        // return new root of the original subtree
        child
    }

    /// # Constraint
    /// - The ancestor of `self` should have no action to propagate.
    pub(crate) fn splay(mut self) {
        self.propagate();
        while let Some(parent) = self.parent {
            let Some(grand_parent) = parent.parent else {
                // zig step
                parent.rotate(parent.left() == Some(self));
                return;
            };

            let sf = parent.left() == Some(self);
            let pf = grand_parent.left() == Some(parent);
            if sf ^ pf {
                // zig-zag step
                parent.rotate(sf);
                grand_parent.rotate(!sf);
            } else {
                // zig-zig step
                grand_parent.rotate(sf);
                parent.rotate(sf);
            }
        }
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

impl<D: NodeData> Eq for NodeRef<D> {}

impl<D: NodeData> PartialOrd for NodeRef<D> {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl<D: NodeData> Ord for NodeRef<D> {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(&other.0)
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
            .field("left", &self.left())
            .field("right", &self.right())
            .finish()
    }
}

pub(crate) struct NodeAllocator<D: NodeData + Default> {
    cnt: usize,
    cap: usize,
    nodes: Vec<Box<[Node<D>]>>,
    ptr: Vec<NodeRef<D>>,
}

impl<D: NodeData + Default> NodeAllocator<D> {
    pub(crate) fn with_capacity(cap: usize) -> Self {
        let cap = cap.max(1);
        let nodes = vec![(0..cap).map(|_| Node::new(D::default())).collect()];
        Self { cnt: 0, cap, nodes, ptr: vec![] }
    }

    pub(crate) fn from_buffer(buf: Box<[Node<D>]>) -> Self {
        if buf.is_empty() {
            return Self::default();
        }
        let nodes = vec![buf];
        Self { cnt: 0, cap: nodes[0].len(), nodes, ptr: vec![] }
    }

    pub(crate) fn alloc_uninitialized(&mut self) -> NodeRef<D> {
        self.ptr.pop().unwrap_or_else(|| {
            if self.cnt < self.nodes.last().unwrap().len() {
                self.cnt += 1;
                let res = unsafe {
                    NodeRef::from_raw_unchecked(
                        self.nodes
                            .last_mut()
                            .unwrap()
                            .as_mut_ptr()
                            .add(self.cnt - 1),
                    )
                };
                return res;
            }

            self.cnt = 0;
            self.nodes
                .push((0..self.cap).map(|_| Node::new(D::default())).collect());
            self.cap <<= 1;

            self.alloc_uninitialized()
        })
    }

    pub(crate) fn alloc(&mut self, data: D) -> NodeRef<D> {
        let mut res = self.alloc_uninitialized();
        res.initialize(data);
        res
    }

    pub(crate) fn dealloc(&mut self, p: NodeRef<D>) {
        self.ptr.push(p);
    }
}

impl<D: NodeData + Default> Default for NodeAllocator<D> {
    fn default() -> Self {
        NodeAllocator::with_capacity(0)
    }
}
