#[cfg(feature = "rustc-hash")]
use rustc_hash::FxHasher;

use crate::DefaultZST;

use super::MapMonoid;

use std::cell::RefCell;
#[cfg(not(feature = "rustc-hash"))]
use std::collections::hash_map::RandomState;
use std::collections::HashMap;
use std::fmt::Debug;
#[cfg(feature = "rustc-hash")]
use std::hash::BuildHasherDefault;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;
use std::rc::Rc;

// Left children are sallower than self, and right children are deeper than self.
struct Node<M: MapMonoid = DefaultZST> {
    parent: Option<NodeRef<M>>,
    left: Option<NodeRef<M>>,
    right: Option<NodeRef<M>>,
    index: usize,
    val: M::M,
    sum: M::M,
    lazy: M::Act,
    size: u32,
    /// 0-bit   : self has some edges
    /// 1-bit   : subtree has some edges
    /// 2-bit   : own layer's edge
    /// 3-bit   : own layer's edge exists on subtree
    flag: u8,
}

impl<M: MapMonoid> Node<M> {
    fn new(src: u32, dest: u32, own_layer: bool) -> Self {
        let index = ((src as usize) << 32) | dest as usize;
        Self {
            parent: None,
            left: None,
            right: None,
            index,
            val: M::e(),
            sum: M::e(),
            lazy: M::id(),
            size: (src == dest) as u32,
            // If this node is not edge, but vertex, it is not 'own layer's edge'
            flag: ((src != dest && own_layer) as u8) << 2,
        }
    }

    fn initialize(&mut self, src: u32, dest: u32, own_layer: bool) {
        self.parent = None;
        self.left = None;
        self.right = None;
        self.index = ((src as usize) << 32) | dest as usize;
        self.val = M::e();
        self.sum = M::e();
        self.lazy = M::id();
        self.size = (src == dest) as u32;
        self.flag = ((src != dest && own_layer) as u8) << 2;
    }

    const fn source(&self) -> usize {
        self.index() >> 32
    }

    const fn destination(&self) -> usize {
        self.index() & 0xFFFFFFFF
    }

    const fn is_self_loop(&self) -> bool {
        self.source() == self.destination()
    }

    pub const fn index(&self) -> usize {
        self.index
    }

    fn propagate(&mut self) {
        if let Some(mut left) = self.left {
            left.lazy = M::composite(&left.lazy, &self.lazy);
            left.val = M::map(&left.val, &self.lazy);
            left.sum = M::map(&left.sum, &self.lazy);
        }
        if let Some(mut right) = self.right {
            right.lazy = M::composite(&right.lazy, &self.lazy);
            right.val = M::map(&right.val, &self.lazy);
            right.sum = M::map(&right.sum, &self.lazy);
        }

        self.lazy = M::id();
    }

    pub(crate) fn update(&mut self) {
        self.sum = match (self.left, self.right) {
            (Some(l), Some(r)) => {
                self.size = l.size + r.size + self.is_self_loop() as u32;
                M::op(&M::op(&l.sum, &self.val), &r.sum)
            }
            (Some(l), _) => {
                self.size = l.size + self.is_self_loop() as u32;
                M::op(&l.sum, &self.val)
            }
            (_, Some(r)) => {
                self.size = r.size + self.is_self_loop() as u32;
                M::op(&self.val, &r.sum)
            }
            _ => {
                self.size = self.is_self_loop() as u32;
                M::op(&self.val, &M::e())
            }
        };

        self.update_flag();
    }

    fn update_flag(&mut self) {
        let b = self.left.map_or(0, |l| l.flag) | self.right.map_or(0, |r| r.flag);
        let b = (b | (b << 1)) & 0b1010;
        self.flag = b | (self.flag & 0b0101);
    }

    fn set_aux_edge(&mut self) {
        self.flag |= 1;
    }

    fn remove_aux_edge(&mut self) {
        self.flag &= !1;
    }

    fn has_aux_edges(&self) -> bool {
        self.flag & 1 != 0
    }

    fn has_aux_edges_subtree(&self) -> bool {
        self.flag & 0b10 != 0
    }

    fn unset_as_own_layers_edge(&mut self) {
        self.flag &= !0b100;
    }

    fn is_own_layers_edge(&self) -> bool {
        self.flag & 0b100 != 0
    }

    fn has_own_laysers_edge_on_subtree(&self) -> bool {
        self.flag & 0b1000 != 0
    }
}

impl<M: MapMonoid> PartialEq for Node<M> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<M> Debug for Node<M>
where
    M: MapMonoid,
    M::M: Debug,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("source", &self.source())
            .field("destination", &self.destination())
            .field("val", &self.val)
            .field("sum", &self.sum)
            .field("lazy", &self.lazy)
            .field("parent", &format!("{:?}", self.parent.map(|p| p.index())))
            .field("left", &self.left)
            .field("right", &self.right)
            .finish()
    }
}

struct NodeRef<M: MapMonoid>(NonNull<Node<M>>);

impl<M: MapMonoid> NodeRef<M> {
    pub(crate) fn connect_left(mut self, mut child: Self) {
        assert_ne!(self.index, child.index);
        self.left = Some(child);
        child.parent = Some(self);
    }

    pub(crate) fn connect_right(mut self, mut child: Self) {
        assert_ne!(self.index, child.index);
        self.right = Some(child);
        child.parent = Some(self);
    }

    fn disconnect_left(mut self) -> Option<Self> {
        let mut left = self.left.take()?;
        left.parent = None;
        Some(left)
    }

    fn disconnect_right(mut self) -> Option<Self> {
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

        right.size = self.size;
        right.sum = M::op(&M::e(), &self.sum);
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
        right.update_flag();

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

        left.size = self.size;
        left.sum = M::op(&M::e(), &self.sum);
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
        left.update_flag();
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

    pub(crate) fn splay(mut self) {
        self.propagate();
        while !self.is_root() {
            let mut parent = self.parent.unwrap();

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

            let mut grand_parent = parent.parent.unwrap();
            grand_parent.propagate();
            parent.propagate();
            self.propagate();
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

    fn is_root(self) -> bool {
        self.parent.is_none()
    }
}

impl<M: MapMonoid> Clone for NodeRef<M> {
    fn clone(&self) -> Self {
        *self
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
        f.debug_struct("NodeRef")
            .field("source", &self.source())
            .field("destination", &self.destination())
            .field("val", &self.val)
            .field("sum", &self.sum)
            .field("lazy", &self.lazy)
            .field("parent", &format!("{:?}", self.parent.map(|p| p.index())))
            .field("left", &self.left)
            .field("right", &self.right)
            .finish()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EttLinkError {
    EdgeAlreadyExists,
    SelfLoop,
    MakeCycle,
}

pub(crate) struct EttNodeAllocator<M: MapMonoid> {
    cnt: usize,
    nodes: Vec<Box<[Node<M>]>>,
    ptr: Vec<NodeRef<M>>,
}

impl<M: MapMonoid> EttNodeAllocator<M> {
    pub(crate) fn with_capacity(cap: usize) -> Self {
        let nodes = (0..cap.max(1)).map(|_| Node::new(0, 0, false)).collect();
        Self { cnt: 0, nodes: vec![nodes], ptr: vec![] }
    }

    fn make_edge(&mut self, src: usize, dest: usize, own_layer: bool) -> NodeRef<M> {
        if let Some(mut p) = self.ptr.pop() {
            p.initialize(src as u32, dest as u32, own_layer);
            p
        } else {
            if self.cnt < self.nodes.last().unwrap().len() {
                self.cnt += 1;
                let mut res = unsafe {
                    NodeRef(NonNull::new_unchecked(
                        self.nodes
                            .last_mut()
                            .unwrap()
                            .as_mut_ptr()
                            .add(self.cnt - 1),
                    ))
                };
                res.initialize(src as u32, dest as u32, own_layer);
                return res;
            }

            self.cnt = 0;
            let newlen = self.nodes.last().unwrap().len() * 2;
            self.nodes
                .push((0..newlen).map(|_| Node::new(0, 0, false)).collect());

            self.make_edge(src, dest, own_layer)
        }
    }

    fn return_edge(&mut self, p: NodeRef<M>) {
        self.ptr.push(p);
    }
}

type EdgesMap<M, S> = HashMap<(usize, usize), (NodeRef<M>, NodeRef<M>), S>;

/// https://web.stanford.edu/class/cs166/lectures/15/Slides15.pdf
///
/// There is no procedure that uses MapMonoid::reverse, so it is meaningless to implement it.
#[cfg(not(feature = "rustc-hash"))]
pub struct EulerTourTree<M: MapMonoid, S = RandomState> {
    vertex: Box<[Node<M>]>,
    edges: EdgesMap<M, S>,
    alloc: Rc<RefCell<EttNodeAllocator<M>>>,
}

/// https://web.stanford.edu/class/cs166/lectures/15/Slides15.pdf
///
/// There is no procedure that uses MapMonoid::reverse, so it is meaningless to implement it.
#[cfg(feature = "rustc-hash")]
pub struct EulerTourTree<M: MapMonoid, S = BuildHasherDefault<FxHasher>> {
    vertex: Box<[Node<M>]>,
    edges: EdgesMap<M, S>,
    alloc: Rc<RefCell<EttNodeAllocator<M>>>,
}

impl<M: MapMonoid> EulerTourTree<M> {
    /// Return the forest that its size is `size`.
    pub fn new(n: usize) -> Self {
        // Because `self.link()` is performed for no edges, this never throws an error.
        Self::from_edges(n, []).unwrap()
    }

    pub(crate) fn new_in(n: usize, alloc: Rc<RefCell<EttNodeAllocator<M>>>) -> Self {
        Self::from_edges_in(n, [], alloc).unwrap()
    }

    /// Consturct the forest that its size is `size` and each vertexes are connected by `edges`.  
    /// Returns an error if it contains multiple edges, self-loops, or has a closed cycle.
    ///
    /// The index of vertexes are 0-index.
    pub fn from_edges(
        n: usize,
        edges: impl IntoIterator<Item = (usize, usize)>,
    ) -> Result<Self, EttLinkError> {
        Self::from_edges_with_values(n, edges, [])
    }

    pub(crate) fn from_edges_in(
        n: usize,
        edges: impl IntoIterator<Item = (usize, usize)>,
        alloc: Rc<RefCell<EttNodeAllocator<M>>>,
    ) -> Result<Self, EttLinkError> {
        Self::from_edges_with_values_in(n, edges, [], alloc)
    }

    pub fn from_edges_with_values(
        n: usize,
        edges: impl IntoIterator<Item = (usize, usize)>,
        values: impl IntoIterator<Item = (usize, M::M)>,
    ) -> Result<Self, EttLinkError> {
        Self::from_edges_with_values_in(
            n,
            edges,
            values,
            Rc::new(RefCell::new(EttNodeAllocator::with_capacity((n - 1) * 2))),
        )
    }

    pub(crate) fn from_edges_with_values_in(
        n: usize,
        edges: impl IntoIterator<Item = (usize, usize)>,
        values: impl IntoIterator<Item = (usize, M::M)>,
        alloc: Rc<RefCell<EttNodeAllocator<M>>>,
    ) -> Result<Self, EttLinkError> {
        let mut vertex = (0..n)
            .map(|i| Node::new(i as u32, i as u32, false))
            .collect::<Box<[_]>>();

        for (i, v) in values {
            vertex[i].val = v;
            vertex[i].update();
        }

        let mut res = Self { vertex, edges: HashMap::default(), alloc };

        for (u, v) in edges {
            res.link(u, v)?;
        }

        Ok(res)
    }

    fn nth_vertex(&self, n: usize) -> NodeRef<M> {
        assert!(n < self.vertex.len());
        unsafe { NodeRef(NonNull::new_unchecked(self.vertex.as_ptr().add(n) as _)) }
    }

    /// Return the most left element on the tree `u` belongs to.  
    /// It is guaranteed that returned element will be the root of the tree.
    fn most_left(&self, u: usize) -> NodeRef<M> {
        let mut res = self.nth_vertex(u);
        res.splay();
        while let Some(left) = res.left {
            res = left;
        }
        res.splay();
        res
    }

    /// Return the most right element on the subtree that `u` is root.
    fn most_right_from(&self, mut r: NodeRef<M>) -> NodeRef<M> {
        while let Some(nr) = r.right {
            r = nr;
        }
        r.splay();
        r
    }

    /// Check if `u` and `v` belong to the same tree.  
    /// If `u == v`, return true.
    pub fn are_connected(&self, u: usize, v: usize) -> bool {
        if u == v || self.edges.contains_key(&(u.min(v), u.max(v))) {
            return true;
        }
        self.nth_vertex(u).splay();
        self.nth_vertex(v).splay();

        !self.nth_vertex(u).is_root()
    }

    /// Make the vertex `new_root` be this tree's root.
    pub fn reroot(&mut self, new_root: usize) {
        self.nth_vertex(new_root).splay();
        self.reroot_inner(new_root);
    }

    /// Perform reroot and return new root element of the inner bbst.  
    /// Only internal use.
    ///
    /// If reroot does not perform, return `None`.
    fn reroot_inner(&mut self, new_root: usize) -> Option<NodeRef<M>> {
        self.vertex[new_root].left.is_some().then(|| {
            self.nth_vertex(new_root).splay();
            let p = self.nth_vertex(new_root).disconnect_left().unwrap();
            self.nth_vertex(new_root).update();
            let mut r = self.most_right_from(self.nth_vertex(new_root));
            r.connect_right(p);
            r.update();
            r
        })
    }

    pub fn link(&mut self, u: usize, v: usize) -> Result<(), EttLinkError> {
        self.link_as_specified_layer(u, v, false)
    }

    /// Connect `u` and `v` by an edge.  
    /// Returns an error if the given edge makes a multiple edge, a self-loop, or a closed cycle.
    pub(crate) fn link_as_specified_layer(
        &mut self,
        u: usize,
        v: usize,
        own_layer: bool,
    ) -> Result<(), EttLinkError> {
        if u == v {
            return Err(EttLinkError::SelfLoop);
        }
        if self.has_edge(u, v) {
            return Err(EttLinkError::EdgeAlreadyExists);
        }
        if self.are_connected(u, v) {
            return Err(EttLinkError::MakeCycle);
        }

        let (u, v) = (u.min(v), u.max(v));

        let mut uv = self.alloc.borrow_mut().make_edge(u, v, own_layer);
        // If reroot is performed, returned element is the root of the tree that `u` belongs to.
        // If not performed, `self.vertex[u]` is the root element because `self.vertex[u]` should be splayed at time of performed `self.are_connected(u, v)`.
        // The same applies to `v`.
        uv.connect_left(self.reroot_inner(u).unwrap_or(self.nth_vertex(u)));
        uv.connect_right(self.reroot_inner(v).unwrap_or(self.nth_vertex(v)));
        uv.update();

        // f one of the own_layer flags is `true`, it is possible to determine whether it is an edge of its own layer, so the other own_layer flag is always false.
        let vu = self.alloc.borrow_mut().make_edge(v, u, false);
        let mr = self.most_right_from(uv);
        mr.connect_right(vu);
        // `vu` has no value, so it is not necessary to call `mr.update()` here.
        vu.splay();

        self.edges.insert((u, v), (uv, vu));
        Ok(())
    }

    /// Diconnect `u` and `v`.
    pub fn cut(&mut self, u: usize, v: usize) {
        if u == v || !self.has_edge(u, v) {
            return;
        }

        let Some((l, r)) = self.edges.remove(&(u.min(v), u.max(v))) else {
            return;
        };

        l.splay();
        match (l.disconnect_left(), l.disconnect_right()) {
            (Some(lc), Some(rc)) => {
                r.splay();
                if !lc.is_root() || lc == r {
                    r.disconnect_right();
                    if let Some(mut l) = r.disconnect_left() {
                        l = self.most_right_from(l);
                        l.connect_right(rc);
                        l.update();
                    }
                } else {
                    r.disconnect_left();
                    if let Some(mut rr) = r.disconnect_right() {
                        while let Some(l) = rr.left {
                            rr = l;
                        }
                        rr.splay();
                        rr.connect_left(lc);
                        rr.update();
                    }
                }
            }
            (Some(_), _) | (_, Some(_)) => {
                r.splay();
                r.disconnect_left();
                r.disconnect_right();
            }
            (None, None) => unreachable!("The pair of a edge is not found"),
        }

        self.alloc.borrow_mut().return_edge(l);
        self.alloc.borrow_mut().return_edge(r);
    }

    /// Return the size of the tree that `u` belongs to.  
    /// This is <strong>NOT subtree size</strong>, but <strong>whole tree size that `u` is belong to</strong>.
    pub fn tree_size(&self, u: usize) -> usize {
        self.nth_vertex(u).splay();
        self.nth_vertex(u).size as usize
    }

    pub(crate) fn set_aux_edge(&mut self, u: usize) {
        if !self.vertex[u].has_aux_edges() {
            self.nth_vertex(u).splay();
            self.vertex[u].set_aux_edge();
            self.vertex[u].update_flag();
        }
    }

    pub(crate) fn remove_aux_edge(&mut self, u: usize) {
        self.nth_vertex(u).splay();
        self.vertex[u].remove_aux_edge();
        self.vertex[u].update_flag();
    }

    /// Search a vertex that has some aux edges on the tree that `u` belongs to.  
    /// If found, return its index. If not, return `None`.
    pub(crate) fn find_vertex_has_aux_edge(&self, u: usize) -> Option<usize> {
        let mut now = self.nth_vertex(u);
        // If some elements of the subtree has aux edges, it is not necessary to move `now` to the root of the tree.
        if !now.has_aux_edges() && !now.has_aux_edges_subtree() {
            now.splay();
        }

        while !now.has_aux_edges() && now.has_aux_edges_subtree() {
            if now
                .left
                .map_or(false, |l| l.has_aux_edges() || l.has_aux_edges_subtree())
            {
                now = now.left.unwrap();
            } else {
                now = now.right.unwrap();
            }
        }

        now.has_aux_edges().then(|| {
            now.splay();
            assert!(now.is_self_loop());
            now.source()
        })
    }

    /// Search an own layer's edge on the tree that `u` belongs to.  
    /// If found, return its pair of the indices. If not, return `None`.
    pub(crate) fn find_and_unset_own_layers_edge(&self, u: usize) -> Option<(usize, usize)> {
        let mut now = self.nth_vertex(u);
        if !now.is_own_layers_edge() && !now.has_own_laysers_edge_on_subtree() {
            now.splay();
        }

        while !now.is_own_layers_edge() && now.has_own_laysers_edge_on_subtree() {
            if now.left.map_or(false, |l| {
                l.is_own_layers_edge() || l.has_own_laysers_edge_on_subtree()
            }) {
                now = now.left.unwrap();
            } else {
                now = now.right.unwrap();
            }
        }

        now.is_own_layers_edge().then(|| {
            now.splay();
            now.unset_as_own_layers_edge();
            now.update_flag();
            assert!(!now.is_self_loop());
            (now.source(), now.destination())
        })
    }

    pub fn euler_tour_with_vertex(&self, u: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
        let mut m = Some(self.most_left(u));

        std::iter::from_fn(move || {
            let n = m.take()?;
            n.splay();

            if let Some(mut next) = n.right {
                while let Some(l) = next.left {
                    next = l;
                }
                m = Some(next);
            }

            Some((n.source(), n.destination()))
        })
    }

    /// Return an Euler Tour sequnce of the tree that `u` belongs to.  
    pub fn euler_tour(&self, u: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.euler_tour_with_vertex(u).filter(|(u, v)| u != v)
    }

    /// Enumerate the edges of the tree that `u` belongs to.  
    pub fn edges(&self, u: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.euler_tour(u).filter(|e| e.0 < e.1)
    }

    /// Enumerate the vertexes of the tree that `u` belongs to.  
    pub fn vertexes(&self, u: usize) -> impl Iterator<Item = usize> + '_ {
        let mut m = Some(self.most_left(u));

        std::iter::from_fn(move || loop {
            let n = m.take()?;
            n.splay();

            if let Some(mut next) = n.right {
                while let Some(l) = next.left {
                    next = l;
                }
                m = Some(next);
            }

            if n.is_self_loop() {
                break Some(n.source());
            }
        })
    }

    /// Check if this tree has the edge `u - v`.  
    /// This structure does not allow any self-loop, so if `u == v`, return `false`.
    pub fn has_edge(&self, u: usize, v: usize) -> bool {
        u != v && self.edges.contains_key(&(u.min(v), u.max(v)))
    }

    /// Fold values of the vertexes of the tree that `u` belongs to.
    pub fn fold(&self, u: usize) -> M::M {
        self.nth_vertex(u).splay();
        M::op(&M::e(), &self.vertex[u].sum)
    }

    pub fn set(&mut self, index: usize, value: M::M) {
        self.nth_vertex(index).splay();
        self.vertex[index].val = value;
        self.vertex[index].update();
    }

    pub fn update_by(&mut self, index: usize, f: impl Fn(&M::M) -> M::M) {
        self.nth_vertex(index).splay();
        self.vertex[index].val = f(&self.vertex[index].val);
        self.vertex[index].update();
    }

    /// Apply the action `act` to the tree that `u` belongs to.
    pub fn apply(&mut self, u: usize, act: &M::Act) {
        self.nth_vertex(u).splay();
        self.vertex[u].val = M::map(&self.vertex[u].val, act);
        self.vertex[u].lazy = M::composite(&self.vertex[u].lazy, act);
        self.vertex[u].propagate();
        self.vertex[u].update();
    }

    /// Apply the action `act` to the tree that `u` belongs to.  
    /// The action affects only the subtree of `u` whose parent is `parent`.
    ///
    /// # Panics
    /// - `self.has_edge(u, parent)` must be `true`.
    pub fn apply_subtree(&mut self, u: usize, parent: usize, act: &M::Act) {
        if !self.has_edge(u, parent) {
            panic!("There is no link between `{u}` and `{parent}`.");
        }
        self.cut(u, parent);
        self.apply(u, act);
        self.link(u, parent).unwrap();
    }

    /// Returns the aggregate value of the subtree whose root is u when `parent` is the parent.
    ///
    /// If `self.has_edge(u, parent)` is `false`, return `None`.
    pub fn fold_subtree(&self, u: usize, parent: usize) -> Option<M::M> {
        let &(mut l, mut r) = self.edges.get(&(u.min(parent), u.max(parent)))?;
        if u < parent {
            (l, r) = (r, l);
        }

        l.splay();
        let (lc, rc) = (l.disconnect_left(), l.disconnect_right());
        r.splay();
        Some(match (lc, rc) {
            (Some(lc), Some(rc)) => {
                if !lc.is_root() || lc == r {
                    l.connect_left(r);
                    l.connect_right(rc);
                    M::op(&rc.sum, &r.left.unwrap().sum)
                } else {
                    l.connect_left(lc);
                    l.connect_right(r);
                    M::op(&M::e(), &r.left.unwrap().sum)
                }
            }
            (Some(_), _) => {
                l.connect_left(r);
                M::op(&M::e(), &r.left.unwrap().sum)
            }
            (_, Some(_)) => {
                l.connect_right(r);
                M::op(&M::e(), &r.left.unwrap().sum)
            }
            _ => unreachable!(),
        })
    }
}

impl<M> Debug for EulerTourTree<M>
where
    M: MapMonoid,
    M::M: Debug,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EulerTourTree")
            .field("vertexes", &self.vertex)
            .field("edges", &self.edges)
            .finish()
    }
}

#[cfg(test)]
mod tests {
    use rand::{thread_rng, Rng};

    use std::collections::HashSet;

    use super::*;

    struct U32Add;
    impl MapMonoid for U32Add {
        type Act = ();
        type M = u32;
        fn e() -> Self::M {
            0
        }
        fn op(l: &Self::M, r: &Self::M) -> Self::M {
            l + r
        }
        fn composite(_: &Self::Act, _: &Self::Act) -> Self::Act {}
        fn id() -> Self::Act {}
        fn map(m: &Self::M, _: &Self::Act) -> Self::M {
            *m
        }
    }

    #[test]
    fn euler_tour_tree_randome_link_cut_test() {
        const V: usize = 20;

        fn has_path(now: usize, tar: usize, memo: &mut [bool], g: &[HashSet<usize>]) -> bool {
            if now == tar {
                return true;
            }
            memo[now] = true;
            for &to in &g[now] {
                if !memo[to] && has_path(to, tar, memo, g) {
                    return true;
                }
            }

            false
        }

        for i in 0..10000 {
            let mut dc = EulerTourTree::<U32Add>::new(V);
            let mut rng = thread_rng();
            let mut g = vec![HashSet::new(); V];
            let mut val = vec![0; V];

            eprintln!("---------------- start iteration {i} ----------------");

            for _ in 0..30 {
                let ty = rng.gen_range(0u8..6);

                match ty {
                    0 => {
                        let u = rng.gen_range(0..V - 1);
                        let v = rng.gen_range(u + 1..V);
                        eprintln!("ty: 0, u: {u}, v: {v}");
                        dc.link(u, v).ok();

                        let mut memo = vec![false; V];
                        if !has_path(u, v, &mut memo, &g) {
                            g[u].insert(v);
                            g[v].insert(u);
                        }
                    }
                    1 => {
                        let u = rng.gen_range(0..V - 1);
                        let v = rng.gen_range(u + 1..V);
                        eprintln!("ty: 1, u: {u}, v: {v}");
                        dc.cut(u, v);
                        g[u].remove(&v);
                        g[v].remove(&u);
                    }
                    2 => {
                        let v = rng.gen_range(0..V);
                        let x = rng.gen_range(1..=5);
                        eprintln!("ty: 2, v: {v}, x: {x}");
                        dc.update_by(v, |m| m + x);
                        val[v] += x;
                    }
                    3 => {
                        let v = rng.gen_range(0..V);
                        eprintln!("ty: 3, v: {v}");
                        let f = dc.fold(v);

                        fn dfs(
                            now: usize,
                            val: &[u32],
                            memo: &mut [bool],
                            g: &[HashSet<usize>],
                        ) -> u32 {
                            let mut res = val[now];
                            memo[now] = true;
                            for &to in &g[now] {
                                if !memo[to] {
                                    res += dfs(to, val, memo, g);
                                }
                            }
                            res
                        }

                        let mut memo = vec![false; V];
                        assert_eq!(f, dfs(v, &val, &mut memo, &g));
                    }
                    4 => {
                        let u = rng.gen_range(0..V - 1);
                        let v = rng.gen_range(u + 1..V);
                        eprintln!("ty: 4, u: {u}, v: {v}");
                        let f = dc.are_connected(u, v);

                        let mut memo = vec![false; V];
                        assert_eq!(f, has_path(u, v, &mut memo, &g));
                    }
                    5 => {
                        let u = rng.gen_range(0..V);
                        eprintln!("ty: 5, u: {u}");
                        let f = dc.tree_size(u);

                        let mut memo = vec![false; V];
                        assert_eq!(
                            f,
                            (0..V)
                                .filter(|&to| {
                                    memo.fill(false);
                                    has_path(u, to, &mut memo, &g)
                                })
                                .count()
                        );
                    }
                    _ => {}
                }
            }
        }
    }

    #[test]
    fn euler_tour_tree_edges_test() {
        let mut ett = EulerTourTree::<U32Add>::new(10);
        ett.link(4, 8).ok();
        ett.link(1, 8).ok();
        ett.link(8, 9).ok();
        ett.link(7, 8).ok();
        ett.link(5, 9).ok();
        ett.link(3, 5).ok();

        let e = ett.euler_tour(1).collect::<Vec<_>>();
        eprintln!("e: {e:?}");
        for f in e.windows(2) {
            assert_eq!(f[0].1, f[1].0);
        }
    }

    #[test]
    fn euler_tour_tree_vertexes_test() {
        let mut ett = EulerTourTree::<U32Add>::new(10);
        ett.link(4, 8).ok();
        ett.link(1, 8).ok();
        ett.link(8, 9).ok();
        ett.link(7, 8).ok();
        ett.link(5, 9).ok();
        ett.link(3, 5).ok();

        let mut v = ett.vertexes(1).collect::<Vec<_>>();
        v.sort();
        assert_eq!(v, vec![1, 3, 4, 5, 7, 8, 9]);

        ett.cut(8, 9);
        let mut v = ett.vertexes(1).collect::<Vec<_>>();
        v.sort();
        assert_eq!(v, vec![1, 4, 7, 8]);

        let mut v = ett.vertexes(9).collect::<Vec<_>>();
        v.sort();
        assert_eq!(v, vec![3, 5, 9]);
    }
}
