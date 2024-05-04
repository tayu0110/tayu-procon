use crate::{DefaultZST, EttLinkError, EttNodeAllocator, EulerTourTree};

use super::MapMonoid;
use std::cell::RefCell;
use std::collections::BTreeSet;
use std::fmt::Debug;
use std::rc::Rc;

enum LayeredForest<M: MapMonoid> {
    Top(EulerTourTree<M>),
    Other(EulerTourTree<DefaultZST>),
}

macro_rules! impl_layerd_forests_method {
    ( $self:tt, { $( $sig:tt )* }, { $( $met:tt )* }) => {
        fn $( $sig )* {
            match $self {
                Self::Top(e) => e. $( $met )*,
                Self::Other(e) => e. $( $met )*,
            }
        }
    };
}

impl<M: MapMonoid> LayeredForest<M> {
    impl_layerd_forests_method!(self, {are_connected(&self, u: usize, v: usize) -> bool}, {are_connected(u, v)});
    impl_layerd_forests_method!(self, {link(&mut self, u: usize, v: usize, own_layer: bool) -> Result<(), EttLinkError>}, {link_as_specified_layer(u, v, own_layer)});
    impl_layerd_forests_method!(self, {has_edge(&self, u: usize, v: usize) -> bool}, {has_edge(u, v)});
    impl_layerd_forests_method!(self, {set_aux_edge(&mut self, u: usize)}, {set_aux_edge(u)});
    impl_layerd_forests_method!(self, {remove_aux_edge(&mut self, u: usize)}, {remove_aux_edge(u)});
    impl_layerd_forests_method!(self, {tree_size(&self, u: usize) -> usize}, {tree_size(u)});
    impl_layerd_forests_method!(self, {find_and_unset_own_layers_edge(&self, u: usize) -> Option<(usize, usize)>}, {find_and_unset_own_layers_edge(u)});
    impl_layerd_forests_method!(self, {find_vertex_has_aux_edge(&self, u: usize) -> Option<usize>}, {find_vertex_has_aux_edge(u)});
    impl_layerd_forests_method!(self, {cut(&mut self, u: usize, v: usize)}, {cut(u, v)});

    fn as_top(&self) -> Option<&EulerTourTree<M>> {
        match self {
            LayeredForest::Top(ett) => Some(ett),
            _ => None,
        }
    }

    fn as_top_mut(&mut self) -> Option<&mut EulerTourTree<M>> {
        match self {
            LayeredForest::Top(ett) => Some(ett),
            _ => None,
        }
    }
}

impl<M> Debug for LayeredForest<M>
where
    M: MapMonoid,
    M::M: Debug,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Top(ett) => write!(f, "{ett:?}"),
            Self::Other(ett) => write!(f, "{ett:?}"),
        }
    }
}

/// https://web.stanford.edu/class/cs166/lectures/16/Slides16.pdf
///
/// There is no procedure that uses MapMonoid::reverse, so it is meaningless to implement it.
pub struct OnlineDynamicConnectivity<M: MapMonoid> {
    size: usize,
    etts: Vec<LayeredForest<M>>,
    aux_edges: Vec<Vec<BTreeSet<usize>>>,
    oalloc: Rc<RefCell<EttNodeAllocator<DefaultZST>>>,
}

impl<M: MapMonoid> OnlineDynamicConnectivity<M> {
    pub fn new(size: usize) -> Self {
        let alloc = Rc::new(RefCell::new(EttNodeAllocator::with_capacity(
            (size - 1) * 2,
        )));
        Self {
            size,
            etts: vec![LayeredForest::Top(EulerTourTree::new_in(
                size,
                Rc::clone(&alloc),
            ))],
            aux_edges: vec![vec![BTreeSet::new(); size]],
            oalloc: Rc::new(RefCell::new(EttNodeAllocator::with_capacity(8))),
        }
    }

    /// Consturct the graph that its size is `size` and each vertexes are connected by `edges`.
    ///
    /// Even if `edges` has some duplicate edges or self-loops, these are ignored.  
    /// As a result, The returned graph is always a simple graph.
    ///
    /// The index of vertexes are 0-index.
    ///
    /// # Panics
    /// - All of the elements of `edges` must be less than `size`.
    pub fn from_edges(size: usize, edges: impl IntoIterator<Item = (usize, usize)>) -> Self {
        Self::from_edges_with_values(size, edges, [])
    }

    /// Consturct the graph that its size is `size` and each vertexes are connected by `edges`.
    ///
    /// Even if `edges` has some duplicate edges or self-loops, these are ignored.  
    /// As a result, The returned graph is always a simple graph.
    ///
    /// Each elements of `values` represents `(index, value)`.
    /// If `index < size` is not satisfied, this method will panic.
    ///
    /// The index of vertexes are 0-index.
    ///
    /// # Panics
    /// - All of the elements of `edges` must be less than `size`.
    /// - All of the first elements of `values` must be less than `size`.
    pub fn from_edges_with_values(
        size: usize,
        edges: impl IntoIterator<Item = (usize, usize)>,
        values: impl IntoIterator<Item = (usize, M::M)>,
    ) -> Self {
        let alloc = Rc::new(RefCell::new(EttNodeAllocator::with_capacity(
            (size - 1) * 2,
        )));
        let mut res = Self {
            size,
            // Because `edges` is empty, `EulerTourTree::from_edges_with_values` never throws an error.
            etts: vec![LayeredForest::Top(
                EulerTourTree::from_edges_with_values_in(size, [], values, alloc).unwrap(),
            )],
            aux_edges: vec![vec![BTreeSet::new(); size]],
            oalloc: Rc::new(RefCell::new(EttNodeAllocator::with_capacity(8))),
        };

        for (u, v) in edges {
            res.link(u, v).ok();
        }

        res
    }

    /// Check if any paths exists between `u` and `v`.  
    /// `self.has_edge()` returns `false` if it is not an adjacent vertex,
    /// but `self.are_connected()` returns `true` if there is a path even if it is not an adjacent vertex.
    ///
    /// # Panics
    /// Both `u < self.size()` and `v < self.size()` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use ds::{OnlineDynamicConnectivity, DefaultZST, EttLinkError};
    ///
    /// // This makes the following graph.
    /// // 0 - 1
    /// // |   |
    /// // 2 - 3
    /// let mut dc = OnlineDynamicConnectivity::<DefaultZST>::from_edges(4, [(0, 1), (2, 3), (1, 3), (0, 2)]);
    /// // edge `0 - 3` does not exist
    /// assert!(!dc.has_edge(0, 3));
    /// // but path `0 - 1 - 3` exist between `0` and `3`
    /// // so this is `true`
    /// assert!(dc.are_connected(0, 3));
    /// ```
    pub fn are_connected(&self, u: usize, v: usize) -> bool {
        self.etts[0].are_connected(u, v)
    }

    /// Connect `u` and `v` by an edge.  
    /// If the given edge makes a duplicate edge or a self-loop, return an error.
    ///
    /// # Panics
    /// - Both `u < self.size()` and `v < self.size()` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use ds::{OnlineDynamicConnectivity, DefaultZST, EttLinkError};
    ///
    /// let mut dc = OnlineDynamicConnectivity::<DefaultZST>::new(4);
    /// // 0 - 1
    /// assert!(dc.link(0, 1).is_ok());
    /// // 0 - 1
    /// // 2 - 3
    /// assert!(dc.link(2, 3).is_ok());
    /// // 0 - 1 - 3 - 2
    /// assert!(dc.link(1, 3).is_ok());
    /// // 0 - 1
    /// // |   |
    /// // 2 - 3
    /// assert!(dc.link(0, 2).is_ok());
    /// // edge `1 - 3` already exists, so returned `Err`.
    /// assert_eq!(dc.link(1, 3), Err(EttLinkError::EdgeAlreadyExists));
    /// // self-loop is not allowed, so return `Err`.
    /// assert_eq!(dc.link(1, 1), Err(EttLinkError::SelfLoop));
    /// ```
    pub fn link(&mut self, u: usize, v: usize) -> Result<(), EttLinkError> {
        match self.etts[0].link(u, v, true) {
            Err(EttLinkError::MakeCycle) => {
                self.add_aux_edge(u, v, 0)?;
            }
            Err(e) => return Err(e),
            _ => {}
        }
        Ok(())
    }

    fn expand_layer(&mut self) {
        self.etts.push(LayeredForest::Other(EulerTourTree::new_in(
            self.size,
            Rc::clone(&self.oalloc),
        )));
        self.aux_edges.push(vec![BTreeSet::new(); self.size]);
    }

    /// Check if the edge `u - v` exists in this graph.
    ///
    /// # Panics
    /// Both `u < self.size()` and `v < self.size()` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use ds::{OnlineDynamicConnectivity, DefaultZST, EttLinkError};
    ///
    /// // This makes the following graph.
    /// // 0 - 1
    /// // |   |
    /// // 2 - 3
    /// let mut dc = OnlineDynamicConnectivity::<DefaultZST>::from_edges(4, [(0, 1), (2, 3), (1, 3), (0, 2)]);
    /// // edge `0 - 1` exists
    /// assert!(dc.has_edge(0, 1));
    /// // edge `2 - 3` exists
    /// assert!(dc.has_edge(2, 3));
    /// // edge `1 - 3` exists
    /// assert!(dc.has_edge(1, 3));
    /// // edge `0 - 2` exists
    /// assert!(dc.has_edge(0, 2));
    /// // edge `0 - 3` does not exist
    /// assert!(!dc.has_edge(0, 3));
    /// // edge `1 - 2` does not exist
    /// assert!(!dc.has_edge(1, 2));
    /// ```
    pub fn has_edge(&self, u: usize, v: usize) -> bool {
        self.etts[0].has_edge(u, v) || self.aux_edges.iter().any(|e| e[u].contains(&v))
    }

    fn add_aux_edge(&mut self, u: usize, v: usize, layer: usize) -> Result<(), EttLinkError> {
        if !self.aux_edges[layer][u].insert(v) {
            return Err(EttLinkError::EdgeAlreadyExists);
        }
        self.aux_edges[layer][v].insert(u);
        self.etts[layer].set_aux_edge(u);
        self.etts[layer].set_aux_edge(v);
        Ok(())
    }

    fn remove_aux_edge(&mut self, u: usize, v: usize, layer: usize) {
        if self.aux_edges[layer][u].is_empty() {
            self.etts[layer].remove_aux_edge(u);
        }
        if self.aux_edges[layer][v].is_empty() {
            self.etts[layer].remove_aux_edge(v);
        }
    }

    /// Disconnect the edge `u - v`.  
    /// If the edge `u - v` does not exist in this graph, do nothing.
    ///
    /// # Panics
    /// - Both `u < self.size()` and `v < self.size()` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use ds::{OnlineDynamicConnectivity, DefaultZST, EttLinkError};
    ///
    /// // This makes the following graph.
    /// // 0 - 1
    /// // |   |
    /// // 2 - 3
    /// let mut dc = OnlineDynamicConnectivity::<DefaultZST>::from_edges(4, [(0, 1), (2, 3), (1, 3), (0, 2)]);
    /// assert!(dc.has_edge(1, 3));
    /// assert!(dc.are_connected(1, 3));
    ///
    /// // cut the edge `1 - 3`
    /// // 0 - 1
    /// // |
    /// // 2 - 3
    /// dc.cut(1, 3);
    /// assert!(!dc.has_edge(1, 3));
    /// assert!(dc.are_connected(1, 3));
    ///
    /// // cut the edge `0 - 2`
    /// // 0 - 1
    /// //
    /// // 2 - 3
    /// dc.cut(0, 2);
    /// assert!(!dc.has_edge(0, 2));
    /// assert!(!dc.are_connected(0, 2));
    ///
    /// // link between `0` and `3`
    /// dc.link(0, 3);
    /// // 0 - 1
    /// //   \
    /// // 2 - 3
    /// assert!(dc.are_connected(1, 3));
    /// assert!(dc.are_connected(2, 1));
    ///
    /// // cut the edge `0 - 1`
    /// dc.cut(0, 1);
    /// // 0   1
    /// //   \
    /// // 2 - 3
    /// assert!(!dc.are_connected(1, 3));
    /// assert!(!dc.are_connected(2, 1));
    /// ```
    pub fn cut(&mut self, mut u: usize, mut v: usize) {
        if u == v {
            return;
        }

        for i in 0..self.etts.len() {
            if self.aux_edges[i][u].remove(&v) {
                self.aux_edges[i][v].remove(&u);
                self.remove_aux_edge(u, v, i);
                return;
            }
        }

        let layers = self.etts.len() + 1;
        for l in 0..layers {
            if l == layers - 1 {
                self.expand_layer();
            }

            if !self.etts[l].has_edge(u, v) {
                for i in (0..l).rev() {
                    if self.etts[i].tree_size(u) > self.etts[i].tree_size(v) {
                        (u, v) = (v, u)
                    }
                    while let Some((a, b)) = self.etts[i].find_and_unset_own_layers_edge(u) {
                        self.etts[i + 1].link(a, b, true).unwrap();
                    }

                    let mut res = None;
                    'b: while let Some(a) = self.etts[i].find_vertex_has_aux_edge(u) {
                        while let Some(b) = self.aux_edges[i][a].pop_first() {
                            self.aux_edges[i][b].remove(&a);
                            self.remove_aux_edge(a, b, i);
                            if self.etts[i].are_connected(b, v) {
                                res = Some((a, b));
                                break 'b;
                            }

                            self.add_aux_edge(a, b, i + 1).unwrap();
                        }
                    }

                    if let Some((a, b)) = res {
                        // edge `a - b` is an aux edge, so this should not be connected in tree.
                        self.etts[..i].iter_mut().for_each(|e| {
                            e.link(a, b, false)
                                .expect("Internal Error, an edge is both tree edge and aux edge")
                        });
                        self.etts[i]
                            .link(a, b, true)
                            .expect("Internal Error, an edge is both tree edge and aux edge");

                        return;
                    }
                }

                return;
            }

            self.etts[l].cut(u, v);
        }
    }

    /// Return the size of the connected component that `u` belongs to.
    pub fn component_size(&self, u: usize) -> usize {
        self.etts[0].tree_size(u)
    }

    /// Returns the number of vertices in the whole graph.
    pub fn size(&self) -> usize {
        self.size
    }

    pub fn vertexes(&self, u: usize) -> impl Iterator<Item = usize> + '_ {
        self.etts[0].as_top().unwrap().vertexes(u)
    }

    pub fn edges(&self, u: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
        self.etts[0].as_top().unwrap().edges(u).chain(
            self.aux_edges
                .iter()
                .flat_map(|e| e.iter().enumerate())
                .flat_map(|(i, s)| s.iter().map(move |&s| (i, s)))
                .filter(|(s, d)| s < d),
        )
    }

    /// Fold values of the vertexes of the tree that `u` belongs to.
    pub fn fold(&self, u: usize) -> M::M {
        let LayeredForest::Top(ett) = &self.etts[0] else {
            unreachable!()
        };
        ett.fold(u)
    }

    /// Set a value to the vertex `index`.
    pub fn set(&mut self, index: usize, value: M::M) {
        self.etts[0].as_top_mut().unwrap().set(index, value);
    }

    pub fn update_by(&mut self, index: usize, f: impl Fn(&M::M) -> M::M) {
        self.etts[0].as_top_mut().unwrap().update_by(index, f);
    }
}

impl<M> Debug for OnlineDynamicConnectivity<M>
where
    M: MapMonoid,
    M::M: Debug,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OnlineDynamicConnectivity")
            .field("etts", &self.etts)
            .field("aux_edges", &format!("{:?}", self.aux_edges).as_str())
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
    fn random_link_cut_test() {
        const V: usize = 10;

        for i in 0..10000 {
            let mut dc = OnlineDynamicConnectivity::<U32Add>::new(V);
            let mut rng = thread_rng();
            let mut g = vec![HashSet::new(); V];
            let mut val = vec![0; V];

            eprintln!("---------------- start iteration {i} ----------------");

            for _ in 0..30 {
                let ty = rng.gen_range(0u8..5);

                match ty {
                    0 => {
                        let u = rng.gen_range(0..V - 1);
                        let v = rng.gen_range(u + 1..V);
                        eprintln!("ty: 0, u: {u}, v: {v}");
                        dc.link(u, v).ok();
                        g[u].insert(v);
                        g[v].insert(u);
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
                        let x = rng.gen_range(1..=10);
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

                        fn dfs(
                            now: usize,
                            tar: usize,
                            memo: &mut [bool],
                            g: &[HashSet<usize>],
                        ) -> bool {
                            memo[now] = true;
                            for &to in &g[now] {
                                if to == tar {
                                    return true;
                                }

                                if !memo[to] && dfs(to, tar, memo, g) {
                                    return true;
                                }
                            }

                            false
                        }

                        let mut memo = vec![false; V];
                        assert_eq!(f, dfs(u, v, &mut memo, &g));
                    }
                    _ => {}
                }
            }
        }
    }

    #[test]
    fn link_cut_test() {
        let mut dc = OnlineDynamicConnectivity::<U32Add>::new(10);
        dc.link(4, 8).ok();
        dc.link(1, 8).ok();
        dc.link(8, 9).ok();
        dc.link(7, 8).ok();
        dc.link(5, 9).ok();
        dc.link(3, 5).ok();
        dc.link(7, 9).ok();
        dc.link(3, 9).ok();
        dc.cut(8, 9);
        assert!(dc.are_connected(1, 5));

        let mut dc = OnlineDynamicConnectivity::<U32Add>::new(10);
        dc.link(6, 8).ok();
        dc.link(5, 9).ok();
        assert!(!dc.are_connected(6, 7));
        dc.link(6, 9).ok();
        dc.link(7, 8).ok();
        dc.link(6, 7).ok();
        dc.link(4, 5).ok();
        dc.cut(6, 9);
        dc.cut(7, 8);
        assert!(!dc.are_connected(8, 9));
        assert!(!dc.are_connected(4, 8));
        assert!(dc.are_connected(6, 7));

        let mut dc = OnlineDynamicConnectivity::<U32Add>::new(10);
        dc.update_by(4, |m| m + 8);
        dc.link(4, 9).ok();
        dc.link(4, 7).ok();
        dc.link(3, 4).ok();
        dc.link(7, 9).ok();
        dc.update_by(8, |m| m + 10);
        dc.link(5, 8).ok();
        dc.link(8, 9).ok();
        dc.cut(4, 9);
        dc.update_by(5, |m| m + 4);
        dc.link(4, 6).ok();
        assert_eq!(dc.fold(3), 22);
        dc.update_by(8, |m| m + 8);
        dc.link(7, 8).ok();
        dc.update_by(7, |m| m + 10);
        dc.update_by(3, |m| m + 1);
        assert_eq!(dc.fold(3), 41);
        dc.link(2, 9).ok();
        dc.cut(4, 7);
        dc.cut(8, 9);
        assert_eq!(dc.fold(3), 9);
        dc.link(0, 7).ok();
        assert_eq!(dc.fold(8), 32);
    }
}
