#![allow(
    clippy::collapsible_else_if,
    clippy::comparison_chain,
    clippy::non_canonical_clone_impl
)]

use super::MapMonoid;
use std::fmt::Debug;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

enum Edge<M: MapMonoid> {
    Light(NodeRef<M>),
    Heavy(NodeRef<M>),
    None,
}

// Left children are sallower than self, and right children are deeper than self.
// The most significant bit (i.e., the 31st bit) of `index` is used as the reverse flag.
#[derive(Debug, PartialEq)]
struct Node<M: MapMonoid> {
    parent: Option<NodeRef<M>>,
    left: Option<NodeRef<M>>,
    right: Option<NodeRef<M>>,
    index: u32,
    val: M::M,
    sum: M::M,
    lazy: M::Act,
}

impl<M: MapMonoid> Node<M> {
    pub fn new(index: usize) -> Self {
        Self {
            parent: None,
            left: None,
            right: None,
            index: index as u32,
            val: M::e(),
            sum: M::e(),
            lazy: M::id(),
        }
    }

    pub const fn index(&self) -> usize {
        (self.index & !(1 << 31)) as usize
    }

    pub const fn is_reversed(&self) -> bool {
        self.index >= (1 << 31)
    }

    pub fn toggle(&mut self) {
        self.index ^= 1 << 31;
        M::reverse(&mut self.sum);
        (self.left, self.right) = (self.right, self.left);
    }

    fn propagate(&mut self) {
        if let Some(mut left) = self.left {
            left.lazy = M::composite(&left.lazy, &self.lazy);
            left.sum = M::map(&left.sum, &self.lazy);
            if self.is_reversed() {
                left.toggle();
            }
        }
        if let Some(mut right) = self.right {
            right.lazy = M::composite(&right.lazy, &self.lazy);
            right.sum = M::map(&right.sum, &self.lazy);
            if self.is_reversed() {
                right.toggle();
            }
        }

        self.lazy = M::id();
        self.index = self.index() as u32;
    }

    fn update(&mut self) {
        self.sum = match (self.left, self.right) {
            (Some(l), Some(r)) => M::op(&M::op(&l.sum, &self.val), &r.sum),
            (Some(l), _) => M::op(&l.sum, &self.val),
            (_, Some(r)) => M::op(&self.val, &r.sum),
            _ => M::map(&self.val, &M::id()),
        }
    }
}

struct NodeRef<M: MapMonoid>(NonNull<Node<M>>);

impl<M: MapMonoid> NodeRef<M> {
    fn new(node: Node<M>) -> Self {
        let reference = Box::leak(Box::new(node));
        Self(NonNull::new(reference as *mut _).unwrap())
    }

    fn connect_left(mut self, mut child: Self) {
        assert_ne!(self.index, child.index);
        self.left = Some(child);
        child.parent = Some(self);
    }

    fn connect_right(mut self, mut child: Self) {
        assert_ne!(self.index, child.index);
        self.right = Some(child);
        child.parent = Some(self);
    }

    /// Connect with the parent via Light Edge. The parent side does not point to self, so only the self side is updated.
    fn weak_connect_parent(mut self, parent: Self) {
        self.parent = Some(parent);
    }

    /// Even if `parent` has a child, it is forced to connect at Heavy Edge.
    /// The original child is disconnected from the Heavy Edge connection and is replaced by a Light Edge connection.
    fn force_connect_parent(mut self, mut parent: Self) {
        parent.right = Some(self);
        self.parent = Some(parent);
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

    fn disconnect_parent(&mut self) -> Edge<M> {
        if let Some(mut parent) = self.parent {
            match (parent.left, parent.right) {
                (Some(l), _) if l == *self => {
                    parent.left = None;
                    self.parent = None;
                }
                (_, Some(r)) if r == *self => {
                    parent.right = None;
                    self.parent = None;
                }
                _ => {
                    // This is a pattern that self connects to its parent through Light-Edge.
                    self.parent = None;
                    return Edge::Light(parent);
                }
            }

            Edge::Heavy(parent)
        } else {
            Edge::None
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
        right.update();

        // If self has a parent, disconnect it
        //        a       c
        //       / \       \
        //      b   d       e
        match par {
            Edge::Heavy(mut par) => {
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
                par.update();
            }
            Edge::Light(par) => {
                // In the case of Light Edge, the parent does not update.
                right.weak_connect_parent(par);
            }
            Edge::None => {}
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
        left.update();
        // If self has a parent, disconnect it
        //        a       b
        //       / \     /
        //      e   c   d
        match par {
            Edge::Heavy(mut par) => {
                // and connect it to left as a parent
                if self_is_shallow {
                    par.connect_left(left);
                } else {
                    par.connect_right(left);
                }
                par.update();
            }
            Edge::Light(par) => {
                // In the case of Light Edge, the parent does not update.
                left.weak_connect_parent(par);
            }
            Edge::None => {}
        }

        // return new root of the original subtree
        left
    }

    fn splay(mut self) {
        self.propagate();
        while !self.is_root() {
            let &(mut parent) = self.parent.as_ref().unwrap();

            if parent.is_root() {
                // zig step
                parent.propagate();
                self.propagate();
                if self.is_left_child() {
                    parent.rotate_right();
                } else {
                    parent.rotate_left();
                }
                return;
            }

            let &(mut grand_parent) = parent.parent.as_ref().unwrap();
            grand_parent.propagate();
            parent.propagate();
            self.propagate();
            if self.is_left_child() ^ parent.is_left_child() {
                // zig-zag step
                if self.is_left_child() {
                    parent.rotate_right();
                    grand_parent.rotate_left();
                } else if self.is_right_child() {
                    parent.rotate_left();
                    grand_parent.rotate_right();
                } else {
                    unreachable!()
                }
            } else {
                // zig-zig step
                if self.is_left_child() {
                    grand_parent.rotate_right();
                    parent.rotate_right();
                } else if self.is_right_child() {
                    grand_parent.rotate_left();
                    parent.rotate_left();
                } else {
                    unreachable!()
                }
            }
        }
    }

    fn is_left_child(self) -> bool {
        self.parent
            .map_or(false, |p| p.left.map_or(false, |l| l.index == self.index))
    }

    fn is_right_child(self) -> bool {
        self.parent
            .map_or(false, |p| p.right.map_or(false, |r| r.index == self.index))
    }

    fn is_root(self) -> bool {
        self.parent.map_or(true, |p| {
            p.left.map_or(true, |s| s != self) && p.right.map_or(true, |d| d != self)
        })
    }
}

impl<M: MapMonoid> Clone for NodeRef<M> {
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<M: MapMonoid> Copy for NodeRef<M> {}

impl<M: MapMonoid> PartialEq for NodeRef<M> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<M: MapMonoid> Deref for NodeRef<M> {
    type Target = Node<M>;
    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl<M: MapMonoid> DerefMut for NodeRef<M> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut() }
    }
}

impl<M> Debug for NodeRef<M>
where
    M: MapMonoid,
    M::M: Debug,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "NodeRef {{ index: {:?}, val: {:?}, sum: {:?}, lazy: {:?}, rev: {:?}, parent: {:?}, left: {:?}, right: {:?} }}",
            self.index(), self.val, self.sum, self.lazy, self.is_reversed(), self.parent.map(|p| p.index()), self.left, self.right
        )
    }
}

pub struct LinkCutTree<M: MapMonoid = DefaultZST> {
    nodes: Vec<NodeRef<M>>,
}

impl<M: MapMonoid> LinkCutTree<M> {
    pub fn new(size: usize) -> Self {
        Self {
            nodes: (0..size).map(|i| NodeRef::new(Node::new(i))).collect(),
        }
    }

    pub fn from_edges(
        n: usize,
        edges: impl IntoIterator<Item = (usize, usize)>,
    ) -> Result<Self, &'static str> {
        let mut res = Self::new(n);

        for (u, v) in edges {
            res.link(u, v)?;
        }

        Ok(res)
    }

    /// Connect the path from `index` to root with Heavy Edge.
    ///
    /// After the call, `index` becomes the root of an internally managed Splay tree. <br/>
    /// The return value is used internally and has no meaning externally. (It is the index of the vertex which was the root before `index` became the root of the Splay tree.)
    pub fn expose(&self, index: usize) -> usize {
        let mut now = self.nodes[index];
        now.splay();
        // Change a child deeper than itself to a connection at Light Edge.
        // After Expose is complete, only its own ancestors will be connected at Heavy Edge.
        now.right = None;
        now.update();
        debug_assert!(now.is_root());
        while let Some(mut parent) = now.parent {
            parent.splay();
            debug_assert!(parent.is_root());
            now.force_connect_parent(parent);
            parent.update();

            now = parent;
        }

        self.nodes[index].splay();
        debug_assert!(self.nodes[index].parent.is_none());
        now.index()
    }

    /// Returns the root of the tree to which `index` belongs.
    pub fn root(&self, index: usize) -> usize {
        self.expose(index);

        let mut now = self.nodes[index];
        while let Some(left) = now.left {
            now = left;
        }

        now.splay();
        now.index()
    }

    /// Determine if `u` and `v` belong to the same tree.
    pub fn is_connected(&self, u: usize, v: usize) -> bool {
        if u == v {
            return true;
        }

        self.expose(u);
        self.expose(v);

        self.nodes[u].parent.is_some()
    }

    /// This method makes `child` connect to `parent` as a child vertex.
    ///
    /// When `parent` and `child` already belong to the same tree, return `Err`.
    ///
    /// # Example
    /// ```rust
    /// use ds::LinkCutTree;
    ///
    /// let mut tree = <LinkCutTree>::new(3);
    /// let ok = tree.link(0, 1);
    /// assert!(ok.is_ok());
    /// assert!(tree.is_connected(0, 1));
    ///
    /// let ok = tree.link(1, 2);
    /// assert!(ok.is_ok());
    /// assert!(tree.is_connected(1, 2));
    /// assert!(tree.is_connected(0, 2));
    ///
    /// // Vertex 0 is an ancestor of vertex 2.
    /// // So, this call is failed.
    /// let bad = tree.link(0, 2);
    /// assert!(bad.is_err());
    /// ```
    pub fn link(&mut self, parent: usize, child: usize) -> Result<(), &'static str> {
        if self.is_connected(parent, child) {
            return Err("These nodes already belong to the same group.");
        }

        self.expose(parent);
        self.expose(child);

        self.nodes[child].force_connect_parent(self.nodes[parent]);
        self.nodes[parent].update();

        Ok(())
    }

    /// Link `u` and `v` with unknown parent-child relationship.  <br/>
    /// In fact, it is equivalent to the operation of Evert `v` and then connect `v` to `u` as a child.
    pub fn link_flat(&mut self, u: usize, v: usize) -> Result<(), &'static str> {
        self.evert(v);
        self.link(u, v)?;
        Ok(())
    }

    /// This method cuts the link between `new_root` and its parent.
    ///
    /// As a result, `new_root` and its descendants become a new tree with `new_root` as its root.
    ///
    /// # Example
    /// ```rust
    /// use ds::LinkCutTree;
    ///
    /// let mut tree = <LinkCutTree>::new(6);
    /// //      0
    /// //     / \
    /// //    1   2
    /// //   / \   \
    /// //  3   4   5
    /// tree.link(0, 1).unwrap();
    /// tree.link(0, 2).unwrap();
    /// tree.link(1, 3).unwrap();
    /// tree.link(1, 4).unwrap();
    /// tree.link(2, 5).unwrap();
    ///
    /// assert!(tree.is_connected(0, 1));
    /// assert!(tree.is_connected(0, 3));
    ///
    /// assert_eq!(tree.root(3), 0);
    /// assert_eq!(tree.root(5), 0);
    ///
    /// // Cut the link between vertex 0 and vertex 1
    /// //      0
    /// //       \
    /// //    1   2
    /// //   / \   \
    /// //  3   4   5
    /// tree.cut(1);
    ///
    /// assert!(!tree.is_connected(0, 1));
    /// assert!(!tree.is_connected(0, 3));
    ///
    /// assert_eq!(tree.root(3), 1);
    /// assert_eq!(tree.root(5), 0);
    /// ```
    pub fn cut(&mut self, new_root: usize) {
        self.expose(new_root);

        self.nodes[new_root].disconnect_left();
        self.nodes[new_root].update();
    }

    /// Try to cut the edge between nodes `u` and `v`.
    /// If there is no direct connection between the nodes, return `Err`.
    pub fn try_cut(&mut self, u: usize, v: usize) -> Result<(), &'static str> {
        self.evert(u);
        self.expose(v);

        if self.nodes[u].parent != Some(self.nodes[v]) {
            return Err("There is no direct connection between node `u` and node `v`.");
        }

        self.nodes[v].disconnect_left();
        self.nodes[v].update();

        Ok(())
    }

    /// Make `new_root` the new root of the tree to which it belongs.
    ///
    /// # Example
    /// ```rust
    /// use ds::LinkCutTree;
    ///
    /// let mut tree = <LinkCutTree>::new(6);
    /// //      0
    /// //     / \
    /// //    1   2
    /// //   / \   \
    /// //  3   4   5
    /// tree.link(0, 1).unwrap();
    /// tree.link(0, 2).unwrap();
    /// tree.link(1, 3).unwrap();
    /// tree.link(1, 4).unwrap();
    /// tree.link(2, 5).unwrap();
    ///
    /// assert_eq!(tree.root(3), 0);
    /// assert_eq!(tree.root(5), 0);
    ///
    /// // Make vertex 1 the new root of this tree.
    /// //      1
    /// //     /|\
    /// //    3 4 0
    /// //         \
    /// //          2
    /// //           \
    /// //            5
    /// tree.evert(1);
    ///
    /// assert_eq!(tree.root(3), 1);
    /// assert_eq!(tree.root(5), 1);
    /// ```
    pub fn evert(&mut self, new_root: usize) {
        self.expose(new_root);
        assert!(self.nodes[new_root].right.is_none());
        self.nodes[new_root].toggle();
        self.nodes[new_root].propagate();
    }

    /// Return the Lowest Common Ancestor of `u` and `v`.
    ///
    /// This method is very slow...so unless you are simply looking for LCA and require very tight memory constraints, you should use `graph::HeavyLightDecomposition::lca`.
    pub fn lca(&self, u: usize, v: usize) -> Option<usize> {
        self.is_connected(u, v).then(|| {
            self.expose(u);
            self.expose(v)
        })
    }

    pub fn set(&mut self, index: usize, val: M::M) {
        self.expose(index);
        self.nodes[index].val = val;
        self.nodes[index].update();
    }

    pub fn val(&self, index: usize) -> Option<&M::M> {
        self.nodes.get(index).as_ref().map(|n| &n.val)
    }

    pub fn update_by(&mut self, index: usize, f: impl Fn(&M::M) -> M::M) {
        let new = f(&self.nodes[index].val);
        self.set(index, new);
    }

    pub fn fold(&mut self, u: usize, v: usize) -> Option<&M::M> {
        self.is_connected(u, v).then(|| {
            self.evert(u);
            assert!(self.nodes[u].is_root());
            self.expose(v);
            &self.nodes[v].sum
        })
    }

    /// Get the parent of `node`.  
    /// If `node` does not have a parent, return `None`.
    ///
    /// # Example
    /// ```rust
    /// use ds::LinkCutTree;
    ///
    /// let mut tree = <LinkCutTree>::new(6);
    /// //      0
    /// //     / \
    /// //    1   2
    /// //   / \   \
    /// //  3   4   5
    /// tree.link(0, 1).unwrap();
    /// tree.link(0, 2).unwrap();
    /// tree.link(1, 3).unwrap();
    /// tree.link(1, 4).unwrap();
    /// tree.link(2, 5).unwrap();
    ///
    /// assert_eq!(tree.parent(0), None);
    /// assert_eq!(tree.parent(1), Some(0));
    /// assert_eq!(tree.parent(2), Some(0));
    /// assert_eq!(tree.parent(3), Some(1));
    /// assert_eq!(tree.parent(4), Some(1));
    /// assert_eq!(tree.parent(5), Some(2));
    /// ```
    pub fn parent(&self, node: usize) -> Option<usize> {
        self.expose(node);
        let mut par = self.nodes[node].left?;
        while let Some(r) = par.right {
            par = r;
        }
        Some(par.index())
    }
}

impl<M: MapMonoid> Drop for LinkCutTree<M> {
    fn drop(&mut self) {
        self.nodes.iter_mut().for_each(|p| unsafe {
            p.parent = None;
            p.left = None;
            p.right = None;
            let _ = Box::from_raw(p.0.as_ptr());
        });
        self.nodes.clear();
    }
}

impl<M> Debug for LinkCutTree<M>
where
    M: MapMonoid,
    M::M: Debug,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "LinkCutTree {{ nodes: {:?} }}", self.nodes)
    }
}

/// If the Link-Cut Tree does not require any operations, this type can be used as a dummy.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct DefaultZST;

impl MapMonoid for DefaultZST {
    type M = ();
    type Act = ();

    fn e() -> Self::M {}
    fn op(_: &Self::M, _: &Self::M) -> Self::M {}
    fn map(_: &Self::M, _: &Self::Act) -> Self::M {}
    fn id() -> Self::Act {}
    fn composite(_: &Self::Act, _: &Self::Act) -> Self::Act {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn link_cut_is_connected_test() {
        let mut lct = <LinkCutTree>::new(6);
        //        0
        //       /
        //      1   2
        //     /     \
        //    3   4   5
        lct.link(0, 1).unwrap();
        lct.link(1, 3).unwrap();
        lct.link(2, 5).unwrap();

        assert!(lct.is_connected(3, 0));
        assert!(!lct.is_connected(3, 2));
        assert!(lct.is_connected(0, 1));

        //        0
        //
        //      1   2
        //     /     \
        //    3   4   5
        lct.cut(1);

        assert!(!lct.is_connected(3, 0));

        //        0
        //         \
        //      1   2
        //     / \   \
        //    3   4   5
        lct.link(0, 2).unwrap();
        lct.link(1, 4).unwrap();

        assert!(lct.is_connected(0, 5));
        assert!(lct.is_connected(4, 3));
    }

    #[test]
    fn evert_test() {
        let mut lct = <LinkCutTree>::new(6);
        //        0
        //       / \
        //      1   2
        //     / \   \
        //    3   4   5
        lct.link(0, 1).unwrap();
        lct.link(0, 2).unwrap();
        lct.link(1, 3).unwrap();
        lct.link(1, 4).unwrap();
        lct.link(2, 5).unwrap();

        for i in 0..6 {
            assert_eq!(lct.root(i), 0);
        }

        //            5
        //           /
        //          2
        //         /
        //        0
        //       /
        //      1
        //     / \
        //    3   4
        lct.evert(5);

        for i in 0..6 {
            assert_eq!(lct.root(i), 5);
        }

        //      1
        //     /|\
        //    3 4 0
        //         \
        //          2
        //           \
        //            5
        lct.evert(1);

        for i in 0..6 {
            assert_eq!(lct.root(i), 1);
        }
    }
}
