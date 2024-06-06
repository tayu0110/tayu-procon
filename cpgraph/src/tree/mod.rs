mod diameter;
mod euler_tour;
mod hld;
mod lca;
mod path;

use crate::{Edge, EdgeFull, FixedGraph};

/// Representation of trees.
///
/// `W` is the weight type, but if no weight is needed, `()` can be used.  
/// If `DIR == false`, it is an undirected tree, if `true`, it is a directed tree.
#[derive(Debug, Clone)]
pub struct FixedTree<W: Clone, const DIR: bool> {
    graph: FixedGraph<W, DIR>,
}

impl<W: Clone, const DIR: bool> FixedTree<W, DIR> {
    /// Construct a tree from an iterator `edges`.  
    /// The number of vertices is estimated from the maximum index of vertices in the iterator.
    ///
    /// Even if the tree is undirected, there is no need to double the edges.
    ///
    /// # Constraint
    /// - The index of the vertex is 0-based.
    /// - The 0th and 1st of each element of `edges` represents end points of an edge.
    /// - All edges must be used in the construction of the tree.
    /// - All vertices must be connected. For example, if the maximum index is 3, then 0,1,2,3 must all be used.
    ///
    /// # Examples
    /// ```
    /// use cpgraph::FixedTree;
    /// type Tree = FixedTree<(), false>;
    ///
    /// assert!(Tree::from_edges([(0, 1, ()), (1, 2, ()), (1, 3, ())]).is_ok());
    ///
    /// // This is invalid because edges make a cycle.
    /// assert!(Tree::from_edges([(0, 1, ()), (1, 2, ()), (0, 2, ())]).is_err());
    /// // This is invalid becanse edges make a valid tree, but vertex `0` is not used.
    /// assert!(Tree::from_edges([(1, 2, ()), (2, 3, ()), (1, 4, ())]).is_err());
    /// ```
    pub fn from_edges(
        edges: impl IntoIterator<Item = (usize, usize, W)>,
    ) -> Result<Self, &'static str> {
        let graph = FixedGraph::from_edges(edges);

        let res = Self { graph };
        res.is_valid_tree()
            .then_some(res)
            .ok_or("Failed to construct FixedTree : Invalid Tree")
    }

    fn is_valid_tree(&self) -> bool {
        self.graph.num_edges() + 1 == self.graph.num_vertexes()
            && (0..self.graph.num_vertexes())
                .filter(|&v| self.graph.edges(v).len() == 0)
                .count()
                == DIR as usize
    }

    /// Enumerate edges connected to vertex `vertex`.
    ///
    /// # Panics
    /// - `vertex < self.num_vertexes()` must be satisfied.
    ///
    /// # Examples
    /// ```
    /// use cpgraph::FixedTree;
    /// type Tree = FixedTree<(), false>;
    ///
    /// let tree = Tree::try_from((5, [(0, 1), (1, 2), (1, 3), (2, 4)])).unwrap();
    /// let mut neighbor = tree.edges(1).map(|e| e.to()).collect::<Vec<_>>();
    /// neighbor.sort();
    ///
    /// // If Tree = FixedTree<(), true>, neighbor will be equal to vec![2, 3].
    /// assert_eq!(neighbor, vec![0, 2, 3]);
    /// ```
    pub fn edges(
        &self,
        vertex: usize,
    ) -> impl Iterator<Item = &'_ Edge<W>> + ExactSizeIterator + '_ {
        self.graph.edges(vertex)
    }

    /// Enumerate all edges belongs to this tree.  
    ///
    /// In the case of an undirected tree,
    /// all pairs of edges with inverted starting and ending points are also returned.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedTree;
    /// type Tree = FixedTree<(), false>;
    ///
    /// let tree = Tree::try_from((5, [(0, 1), (1, 2), (1, 3), (2, 4)])).unwrap();
    /// let mut edges = tree.edges_all().map(|e| (e.from(), e.to())).collect::<Vec<_>>();
    /// edges.sort();
    ///
    /// assert_eq!(edges, vec![(0, 1), (1, 0), (1, 2), (1, 3), (2, 1), (2, 4), (3, 1), (4, 2)]);
    /// ```
    pub fn edges_all(&self) -> impl Iterator<Item = EdgeFull<'_, W>> + '_ {
        self.graph.edges_all()
    }

    /// Return the number of edges belongs to this tree.  
    /// This value is always equal to `self.num_vertexes().saturating_sub(1)`.
    pub fn num_edges(&self) -> usize {
        self.graph.num_vertexes().saturating_sub(1)
    }

    /// Return the number of vertexes belongs to this tree.
    pub fn num_vertexes(&self) -> usize {
        self.graph.num_vertexes()
    }

    /// Return the `nth`-th edge connected to `vertex`.  
    /// If `nth >= self.edges(vertex).len()` is satisfied, return `None`.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedTree;
    /// type Tree = FixedTree<(), false>;
    ///
    /// let tree = Tree::try_from((5, [(0, 1), (1, 2), (1, 3), (2, 4)])).unwrap();
    /// assert_eq!(tree.nth_edge(0, 0).map(|e| e.to()), Some(1));
    /// assert_eq!(tree.nth_edge(0, 1).map(|e| e.to()), None);
    /// ```
    pub fn nth_edge(&self, vertex: usize, nth: usize) -> Option<&Edge<W>> {
        self.graph.nth_edge(vertex, nth)
    }
}

impl<W: Clone, const DIR: bool> AsRef<FixedGraph<W, DIR>> for FixedTree<W, DIR> {
    fn as_ref(&self) -> &FixedGraph<W, DIR> {
        &self.graph
    }
}

impl<W: Clone, const DIR: bool> AsMut<FixedGraph<W, DIR>> for FixedTree<W, DIR> {
    fn as_mut(&mut self) -> &mut FixedGraph<W, DIR> {
        &mut self.graph
    }
}

impl<W, I, const DIR: bool> TryFrom<(usize, I)> for FixedTree<W, DIR>
where
    W: Clone,
    I: IntoIterator,
    FixedGraph<W, DIR>: FromIterator<I::Item>,
{
    type Error = &'static str;

    /// Construct a tree from a combination of `(size, edges)`.
    ///
    /// # Constraint
    /// - The elements of the iterator must be edges that construct a tree with `value.0` vertices.
    /// - The index of the vertex must be in the range `0..value.0`.
    fn try_from(value: (usize, I)) -> Result<Self, Self::Error> {
        let (n, value) = value;
        let graph = value.into_iter().collect::<FixedGraph<W, DIR>>();

        let res = Self { graph };
        (n == res.num_vertexes() && res.is_valid_tree())
            .then_some(res)
            .ok_or("Failed to construct FixedTree : Invalid Tree")
    }
}
