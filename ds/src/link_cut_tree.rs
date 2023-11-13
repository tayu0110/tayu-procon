#![allow(clippy::collapsible_else_if, clippy::comparison_chain)]

use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

enum Edge {
    Light(NodeRef),
    Heavy(NodeRef),
    None,
}

// Left children are sallower than self, and right children are deeper than self.
// If the index is negative, it is assumed to have the REVERSE flag.
#[derive(Debug, PartialEq)]
struct Node {
    parent: Option<NodeRef>,
    left: Option<NodeRef>,
    right: Option<NodeRef>,
    index: i32,
}

impl Node {
    pub const fn new(index: usize) -> Self {
        Self { parent: None, left: None, right: None, index: index as i32 }
    }

    pub const fn index(&self) -> usize { self.index.unsigned_abs() as usize }

    pub const fn is_reversed(&self) -> bool { self.index < 0 }

    pub fn toggle(&mut self) {
        self.index = -self.index;
        std::mem::swap(&mut self.left, &mut self.right);
    }

    fn propagate(&mut self) {
        if self.is_reversed() {
            std::mem::swap(&mut self.left, &mut self.right);

            if let Some(mut left) = self.left {
                left.toggle();
            }
            if let Some(mut right) = self.right {
                right.toggle();
            }

            self.toggle();
        }
    }
}

#[derive(Debug, PartialEq)]
struct NodeRef(NonNull<Node>);

impl NodeRef {
    fn new(node: Node) -> Self {
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
    fn weak_connect_parent(mut self, parent: Self) { self.parent = Some(parent); }

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

    fn disconnect_parent(&mut self) -> Edge {
        if let Some(mut parent) = self.parent {
            match (parent.left, parent.right) {
                (Some(l), _) if l.index == self.index => {
                    parent.left = None;
                    self.parent = None;
                }
                (_, Some(r)) if r.index == self.index => {
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

        let self_is_shallow = self.is_left_child();
        // If self has a parent, disconnect it
        //        a       c
        //       / \       \
        //      b   d       e
        match self.disconnect_parent() {
            Edge::Heavy(par) => {
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
            Edge::Light(par) => {
                // In the case of Light Edge, the parent does not update.
                right.weak_connect_parent(par);
            }
            Edge::None => {}
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

        let self_is_shallow = self.is_left_child();
        // If self has a parent, disconnect it
        //        a       b
        //       / \     /
        //      e   c   d
        match self.disconnect_parent() {
            Edge::Heavy(par) => {
                // and connect it to left as a parent
                if self_is_shallow {
                    par.connect_left(left);
                } else {
                    par.connect_right(left);
                }
            }
            Edge::Light(par) => {
                // In the case of Light Edge, the parent does not update.
                left.weak_connect_parent(par);
            }
            Edge::None => {}
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

    fn splay(mut self) {
        while !self.is_root() {
            let &(mut parent) = self.parent.as_ref().unwrap();

            if parent.is_root() {
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

impl Clone for NodeRef {
    fn clone(&self) -> Self { Self(self.0) }
}

impl Copy for NodeRef {}

impl Deref for NodeRef {
    type Target = Node;
    fn deref(&self) -> &Self::Target { unsafe { self.0.as_ref() } }
}

impl DerefMut for NodeRef {
    fn deref_mut(&mut self) -> &mut Self::Target { unsafe { self.0.as_mut() } }
}

pub struct LinkCutTree {
    nodes: Vec<NodeRef>,
}

impl LinkCutTree {
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

    pub fn expose(&self, index: usize) -> usize {
        let mut now = self.nodes[index];
        now.splay();
        // Change a child deeper than itself to a connection at Light Edge.
        // After Expose is complete, only its own ancestors will be connected at Heavy Edge.
        now.right = None;
        debug_assert!(now.is_root());
        while let Some(parent) = now.parent {
            parent.splay();
            debug_assert!(parent.is_root());
            now.force_connect_parent(parent);

            now = parent;
        }

        self.nodes[index].splay();
        debug_assert!(self.nodes[index].parent.is_none());
        now.index()
    }

    pub fn root(&self, index: usize) -> usize {
        self.expose(index);

        let mut now = self.nodes[index];
        while let Some(left) = now.left {
            now = left;
        }

        now.splay();
        now.index()
    }

    pub fn is_connected(&mut self, u: usize, v: usize) -> bool {
        if u == v {
            return true;
        }

        self.expose(u);
        self.expose(v);

        self.nodes[u].parent.is_some()
    }

    pub fn link(&mut self, parent: usize, child: usize) -> Result<(), &'static str> {
        if self.is_connected(parent, child) {
            return Err("These nodes already belong to the same group.");
        }

        self.expose(parent);
        self.expose(child);

        self.nodes[child].force_connect_parent(self.nodes[parent]);

        Ok(())
    }

    pub fn cut(&mut self, new_root: usize) {
        self.expose(new_root);

        self.nodes[new_root].disconnect_left();
    }

    pub fn evert(&mut self, new_root: usize) {
        self.expose(new_root);
        self.nodes[new_root].toggle();
        self.nodes[new_root].propagate();
    }

    pub fn lca(&self, u: usize, v: usize) -> usize {
        self.expose(u);
        self.expose(v)
    }
}

impl Drop for LinkCutTree {
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn link_cut_is_connected_test() {
        let mut lct = LinkCutTree::new(6);
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
        let mut lct = LinkCutTree::new(6);
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
