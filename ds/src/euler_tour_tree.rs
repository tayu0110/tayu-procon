#[cfg(feature = "rustc-hash")]
use rustc_hash::FxHasher;

use crate::splay_tree::{Node, NodeAllocator, NodeData, NodeRef};
use crate::DefaultZST;

use super::MapMonoid;

use std::cell::RefCell;
#[cfg(not(feature = "rustc-hash"))]
use std::collections::hash_map::RandomState;
use std::collections::HashMap;
use std::fmt::Debug;
#[cfg(feature = "rustc-hash")]
use std::hash::BuildHasherDefault;
use std::rc::Rc;

pub(crate) struct EttData<M: MapMonoid = DefaultZST> {
    index: usize,
    val: M::M,
    sum: M::M,
    lazy: M::Act,
    size: u32,
    /// 0-bit   : self has some edges
    /// 1-bit   : subtree (include self) has some edges
    /// 2-bit   : own layer's edge
    /// 3-bit   : own layer's edge exists on subtree (include self)
    flag: u8,
}

impl<M: MapMonoid> EttData<M> {
    fn new(src: usize, dest: usize, own_layer: bool) -> Self {
        debug_assert!(src.max(dest) <= 0xFFFFFFFF);
        let index = (src << 32) | dest;
        // If this node is not edge, but vertex, it is not 'own layer's edge'
        let own_layer = (src != dest && own_layer) as u8;
        Self {
            index,
            val: M::e(),
            sum: M::e(),
            lazy: M::id(),
            size: (src == dest) as u32,
            flag: (own_layer << 2) | (own_layer << 3),
        }
    }

    fn source(&self) -> usize {
        self.index() >> 32
    }

    fn destination(&self) -> usize {
        self.index() & 0xFFFFFFFF
    }

    fn is_self_loop(&self) -> bool {
        self.source() == self.destination()
    }
}

impl<M: MapMonoid> NodeData for EttData<M> {
    fn index(&self) -> usize {
        self.index
    }

    fn propagate(&mut self, left: Option<NodeRef<Self>>, right: Option<NodeRef<Self>>) {
        if let Some(mut left) = left {
            left.data.lazy = M::composite(&left.data.lazy, &self.lazy);
            left.data.val = M::map(&left.data.val, &self.lazy);
            left.data.sum = M::map(&left.data.sum, &self.lazy);
        }
        if let Some(mut right) = right {
            right.data.lazy = M::composite(&right.data.lazy, &self.lazy);
            right.data.val = M::map(&right.data.val, &self.lazy);
            right.data.sum = M::map(&right.data.sum, &self.lazy);
        }

        self.lazy = M::id();
    }

    fn update(&mut self, left: Option<NodeRef<Self>>, right: Option<NodeRef<Self>>) {
        self.sum = match (left, right) {
            (Some(l), Some(r)) => {
                self.size = l.data.size + r.data.size + self.is_self_loop() as u32;
                let b = (l.data.flag | r.data.flag | (self.flag << 1)) & 0b1010;
                self.flag = b | (self.flag & 0b0101);
                M::op(&M::op(&l.data.sum, &self.val), &r.data.sum)
            }
            (Some(l), _) => {
                self.size = l.data.size + self.is_self_loop() as u32;
                let b = (l.data.flag | (self.flag << 1)) & 0b1010;
                self.flag = b | (self.flag & 0b0101);
                M::op(&l.data.sum, &self.val)
            }
            (_, Some(r)) => {
                self.size = r.data.size + self.is_self_loop() as u32;
                let b = (r.data.flag | (self.flag << 1)) & 0b1010;
                self.flag = b | (self.flag & 0b0101);
                M::op(&self.val, &r.data.sum)
            }
            _ => {
                self.size = self.is_self_loop() as u32;
                let b = (self.flag << 1) & 0b1010;
                self.flag = b | (self.flag & 0b0101);
                M::op(&self.val, &M::e())
            }
        };
    }

    fn aggrmove(&mut self, source: NodeRef<Self>) {
        self.size = source.data.size;
        self.sum = M::op(&M::e(), &source.data.sum);
        self.flag |= source.data.flag & 0b1010;
    }
}

impl<M: MapMonoid> Default for EttData<M> {
    fn default() -> Self {
        Self {
            index: 0,
            val: M::e(),
            sum: M::e(),
            lazy: M::id(),
            size: 0,
            flag: 0,
        }
    }
}

impl<M: MapMonoid> PartialEq for EttData<M> {
    fn eq(&self, other: &Self) -> bool {
        self.index == other.index
    }
}

impl<M> Debug for EttData<M>
where
    M: MapMonoid,
    M::M: Debug,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("EttData")
            .field("source", &self.source())
            .field("destination", &self.destination())
            .field("size", &self.size)
            .field("val", &self.val)
            .field("sum", &self.sum)
            .field("lazy", &self.lazy)
            .finish()
    }
}

impl<M: MapMonoid> NodeRef<EttData<M>> {
    fn set_aux_edge(mut self) {
        self.data.flag |= 0b11;
    }

    fn remove_aux_edge(mut self) {
        self.data.flag &= !0b11;
        self.update_flag();
    }

    fn has_aux_edges(self) -> bool {
        self.data.flag & 1 != 0
    }

    fn has_aux_edges_subtree(self) -> bool {
        self.data.flag & 0b10 != 0
    }

    fn unset_as_own_layers_edge(mut self) {
        self.data.flag &= !0b1100;
        self.update_flag();
    }

    fn is_own_layers_edge(self) -> bool {
        self.data.flag & 0b100 != 0
    }

    fn has_own_laysers_edge_on_subtree(self) -> bool {
        self.data.flag & 0b1000 != 0
    }

    fn update_flag(mut self) {
        self.data.flag = ((self.left().map_or(0, |l| l.data.flag)
            | self.right().map_or(0, |r| r.data.flag)
            | (self.data.flag << 1))
            & 0b1010)
            | (self.data.flag & 0b0101);
    }

    fn splay_with_propagate(self) {
        self.propagate_all();
        self.splay();
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EttLinkError {
    EdgeAlreadyExists,
    SelfLoop,
    MakeCycle,
}

type EdgesMap<M, S> = HashMap<(usize, usize), (NodeRef<EttData<M>>, NodeRef<EttData<M>>), S>;

/// https://web.stanford.edu/class/cs166/lectures/15/Slides15.pdf
///
/// There is no procedure that uses MapMonoid::reverse, so it is meaningless to implement it.
#[cfg(not(feature = "rustc-hash"))]
pub struct EulerTourTree<M: MapMonoid, S = RandomState> {
    vertex: Box<[Node<EttData<M>>]>,
    edges: EdgesMap<M, S>,
    alloc: Rc<RefCell<NodeAllocator<EttData<M>>>>,
}

/// https://web.stanford.edu/class/cs166/lectures/15/Slides15.pdf
///
/// There is no procedure that uses MapMonoid::reverse, so it is meaningless to implement it.
#[cfg(feature = "rustc-hash")]
pub struct EulerTourTree<M: MapMonoid, S = BuildHasherDefault<FxHasher>> {
    vertex: Box<[Node<EttData<M>>]>,
    edges: EdgesMap<M, S>,
    alloc: Rc<RefCell<NodeAllocator<EttData<M>>>>,
}

impl<M: MapMonoid> EulerTourTree<M> {
    /// Return the forest that its size is `size`.
    pub fn new(n: usize) -> Self {
        // Because `self.link()` is performed for no edges, this never throws an error.
        Self::from_edges(n, []).unwrap()
    }

    pub(crate) fn new_in(n: usize, alloc: Rc<RefCell<NodeAllocator<EttData<M>>>>) -> Self {
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
        alloc: Rc<RefCell<NodeAllocator<EttData<M>>>>,
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
            Rc::new(RefCell::new(NodeAllocator::with_capacity((n - 1) * 2))),
        )
    }

    pub(crate) fn from_edges_with_values_in(
        n: usize,
        edges: impl IntoIterator<Item = (usize, usize)>,
        values: impl IntoIterator<Item = (usize, M::M)>,
        alloc: Rc<RefCell<NodeAllocator<EttData<M>>>>,
    ) -> Result<Self, EttLinkError> {
        let mut vertex = (0..n)
            .map(|i| Node::new(EttData::new(i, i, false)))
            .collect::<Box<[_]>>();

        for (i, v) in values {
            vertex[i].data.val = v;
            vertex[i].update();
        }

        let mut res = Self { vertex, edges: HashMap::default(), alloc };

        for (u, v) in edges {
            res.link(u, v)?;
        }

        Ok(res)
    }

    fn nth_vertex(&self, n: usize) -> NodeRef<EttData<M>> {
        assert!(n < self.vertex.len());
        unsafe { NodeRef::from_raw_unchecked(self.vertex.as_ptr().add(n) as _) }
    }

    /// Return the most left element on the tree `u` belongs to.  
    /// It is guaranteed that returned element will be the root of the tree.
    fn most_left(&self, u: usize) -> NodeRef<EttData<M>> {
        let mut res = self.nth_vertex(u);
        res.splay_with_propagate();
        while let Some(left) = res.left() {
            res = left;
            res.propagate();
        }
        res.splay();
        res
    }

    /// Return the most left element on the subtree that `u` is root.
    fn most_left_from(&self, mut r: NodeRef<EttData<M>>) -> NodeRef<EttData<M>> {
        r.propagate();
        while let Some(nr) = r.left() {
            r = nr;
            r.propagate();
        }
        r.splay();
        r
    }

    /// Return the most right element on the subtree that `u` is root.
    fn most_right_from(&self, mut r: NodeRef<EttData<M>>) -> NodeRef<EttData<M>> {
        r.propagate();
        while let Some(nr) = r.right() {
            r = nr;
            r.propagate();
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
        self.nth_vertex(u).splay_with_propagate();
        self.nth_vertex(v).splay_with_propagate();

        !self.nth_vertex(u).is_root()
    }

    /// Make the vertex `new_root` be this tree's root.
    pub fn reroot(&mut self, new_root: usize) {
        self.nth_vertex(new_root).splay_with_propagate();
        self.reroot_inner(new_root);
    }

    /// Perform reroot and return new root element of the inner bbst.  
    /// Only internal use.
    ///
    /// If reroot does not perform, return `None`.
    fn reroot_inner(&mut self, new_root: usize) -> Option<NodeRef<EttData<M>>> {
        self.vertex[new_root].left().is_some().then(|| {
            self.nth_vertex(new_root).splay_with_propagate();
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

        let mut uv = self.alloc.borrow_mut().alloc(EttData::new(u, v, own_layer));
        // If reroot is performed, returned element is the root of the tree that `u` belongs to.
        // If not performed, `self.vertex[u]` is the root element because `self.vertex[u]` should be splayed at time of performed `self.are_connected(u, v)`.
        // The same applies to `v`.
        uv.connect_left(self.reroot_inner(u).unwrap_or(self.nth_vertex(u)));
        uv.connect_right(self.reroot_inner(v).unwrap_or(self.nth_vertex(v)));
        uv.update();

        // f one of the own_layer flags is `true`, it is possible to determine whether it is an edge of its own layer, so the other own_layer flag is always false.
        let vu = self.alloc.borrow_mut().alloc(EttData::new(v, u, false));
        let mr = self.most_right_from(uv);
        mr.connect_right(vu);
        // `vu` has no value, so it is not necessary to call `mr.update()` here.
        vu.splay_with_propagate();

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

        l.splay_with_propagate();
        match (l.disconnect_left(), l.disconnect_right()) {
            (Some(lc), Some(rc)) => {
                r.splay_with_propagate();
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
                        rr = self.most_left_from(rr);
                        rr.connect_left(lc);
                        rr.update();
                    }
                }
            }
            (Some(_), _) | (_, Some(_)) => {
                r.splay_with_propagate();
                r.disconnect_left();
                r.disconnect_right();
            }
            (None, None) => unreachable!("The pair of a edge is not found"),
        }

        self.alloc.borrow_mut().dealloc(l);
        self.alloc.borrow_mut().dealloc(r);
    }

    /// Return the size of the tree that `u` belongs to.  
    /// This is <strong>NOT subtree size</strong>, but <strong>whole tree size that `u` is belong to</strong>.
    pub fn tree_size(&self, u: usize) -> usize {
        self.nth_vertex(u).splay_with_propagate();
        self.nth_vertex(u).data.size as usize
    }

    pub(crate) fn set_aux_edge(&mut self, u: usize) {
        if !self.nth_vertex(u).has_aux_edges() {
            self.nth_vertex(u).splay_with_propagate();
            self.nth_vertex(u).set_aux_edge();
        }
    }

    pub(crate) fn remove_aux_edge(&mut self, u: usize) {
        self.nth_vertex(u).splay_with_propagate();
        self.nth_vertex(u).remove_aux_edge();
    }

    /// Search a vertex that has some aux edges on the tree that `u` belongs to.  
    /// If found, return its index. If not, return `None`.
    pub(crate) fn find_vertex_has_aux_edge(&self, u: usize) -> Option<usize> {
        let mut now = self.nth_vertex(u);
        // If some elements of the subtree has aux edges, it is not necessary to move `now` to the root of the tree.
        if !now.has_aux_edges() && !now.has_aux_edges_subtree() {
            now.propagate_all();
            now.splay();
        }

        while !now.has_aux_edges() && now.has_aux_edges_subtree() {
            if now
                .left()
                .is_some_and(|l| l.has_aux_edges() || l.has_aux_edges_subtree())
            {
                now = now.left().unwrap();
            } else {
                now = now.right().unwrap();
            }
        }

        now.has_aux_edges().then(|| {
            now.splay_with_propagate();
            assert!(now.data.is_self_loop());
            now.data.source()
        })
    }

    /// Search an own layer's edge on the tree that `u` belongs to.  
    /// If found, return its pair of the indices. If not, return `None`.
    pub(crate) fn find_and_unset_own_layers_edge(&self, u: usize) -> Option<(usize, usize)> {
        let mut now = self.nth_vertex(u);
        if !now.is_own_layers_edge() && !now.has_own_laysers_edge_on_subtree() {
            now.splay_with_propagate();
        }

        while !now.is_own_layers_edge() && now.has_own_laysers_edge_on_subtree() {
            if now
                .left()
                .is_some_and(|l| l.is_own_layers_edge() || l.has_own_laysers_edge_on_subtree())
            {
                now = now.left().unwrap();
            } else {
                now = now.right().unwrap();
            }
        }

        now.is_own_layers_edge().then(|| {
            now.splay_with_propagate();
            now.unset_as_own_layers_edge();
            assert!(!now.data.is_self_loop());
            (now.data.source(), now.data.destination())
        })
    }

    pub fn euler_tour_with_vertex(&self, u: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
        let mut m = Some(self.most_left(u));

        std::iter::from_fn(move || {
            let n = m.take()?;
            n.splay_with_propagate();

            if let Some(next) = n.right() {
                m = Some(self.most_left_from(next));
            }

            Some((n.data.source(), n.data.destination()))
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
            n.splay_with_propagate();

            if let Some(next) = n.right() {
                m = Some(self.most_left_from(next));
            }

            if n.data.is_self_loop() {
                break Some(n.data.source());
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
        self.nth_vertex(u).splay_with_propagate();
        M::op(&M::e(), &self.vertex[u].data.sum)
    }

    pub fn set(&mut self, index: usize, value: M::M) {
        self.nth_vertex(index).splay_with_propagate();
        self.vertex[index].data.val = value;
        self.vertex[index].update();
    }

    pub fn update_by(&mut self, index: usize, f: impl Fn(&M::M) -> M::M) {
        self.nth_vertex(index).splay_with_propagate();
        self.vertex[index].data.val = f(&self.vertex[index].data.val);
        self.vertex[index].update();
    }

    /// Apply the action `act` to the tree that `u` belongs to.
    pub fn apply(&mut self, u: usize, act: &M::Act) {
        self.nth_vertex(u).splay_with_propagate();
        self.vertex[u].data.val = M::map(&self.vertex[u].data.val, act);
        self.vertex[u].data.lazy = M::composite(&self.vertex[u].data.lazy, act);
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

        l.splay_with_propagate();
        let (lc, rc) = (l.disconnect_left(), l.disconnect_right());
        r.splay_with_propagate();
        Some(match (lc, rc) {
            (Some(lc), Some(rc)) => {
                if !lc.is_root() || lc == r {
                    l.connect_left(r);
                    l.connect_right(rc);
                    M::op(&rc.data.sum, &r.left().unwrap().data.sum)
                } else {
                    l.connect_left(lc);
                    l.connect_right(r);
                    M::op(&M::e(), &r.left().unwrap().data.sum)
                }
            }
            (Some(_), _) => {
                l.connect_left(r);
                M::op(&M::e(), &r.left().unwrap().data.sum)
            }
            (_, Some(_)) => {
                l.connect_right(r);
                M::op(&M::e(), &r.left().unwrap().data.sum)
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

    struct U64Add;

    impl MapMonoid for U64Add {
        type M = (u64, u64);
        type Act = u64;
        fn e() -> Self::M {
            (0, 0)
        }
        fn op(l: &Self::M, r: &Self::M) -> Self::M {
            (l.0 + r.0, l.1 + r.1)
        }
        fn id() -> Self::Act {
            0
        }
        fn composite(l: &Self::Act, r: &Self::Act) -> Self::Act {
            l + r
        }
        fn map(m: &Self::M, act: &Self::Act) -> Self::M {
            (m.0 + act * m.1, m.1)
        }
    }

    #[test]
    fn euler_tour_tree_subtree_add_subtree_sum_test() {
        let mut ett = EulerTourTree::<U64Add>::from_edges_with_values(
            5,
            [(0, 1), (1, 2), (2, 3), (1, 4)],
            [
                (0, (1, 1)),
                (1, (10, 1)),
                (2, (100, 1)),
                (3, (1000, 1)),
                (4, (10000, 1)),
            ],
        )
        .unwrap();

        assert_eq!(ett.fold_subtree(1, 0).unwrap().0, 11110);
        ett.apply_subtree(1, 4, &100000);
        assert_eq!(ett.fold_subtree(2, 3).unwrap().0, 310111);
        ett.cut(1, 2);
        ett.link(2, 0).unwrap();
        assert_eq!(ett.fold_subtree(0, 2).unwrap().0, 210011);
        ett.cut(2, 3);
        ett.link(3, 1).unwrap();
        assert_eq!(ett.fold_subtree(1, 4).unwrap().0, 401111);
    }
}
