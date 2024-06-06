use std::fmt::Debug;

use crate::{FixedTree, SaturatingOps};

pub struct Diameter<W: Clone> {
    cost: W,
    path: Vec<usize>,
}

impl<W: Clone> Diameter<W> {
    /// Return the number of vertexes contained in a path.
    pub fn num_vertexes(&self) -> usize {
        self.path.len()
    }

    /// Return the number of vertexes contained in a path.
    pub fn num_edges(&self) -> usize {
        self.path.len().saturating_sub(1)
    }

    /// Return the sum of weights of all edges contained in a path.
    pub fn cost(&self) -> W {
        self.cost.clone()
    }

    /// Return all vertexes contained in a path.
    pub fn path(&self) -> impl Iterator<Item = usize> + '_ {
        self.path.iter().cloned()
    }
}

impl<W> FixedTree<W, false>
where
    W: Clone + Default + SaturatingOps + Ord + Debug,
{
    /// Find the diameter of the tree.  
    /// The number of vertices, vertices in the diameter, cost, etc. are obtained from the returned `Diameter`.
    ///
    /// The sum of `W`, not the number of sides, is used to calculate the diameter.  
    /// To find the diameter based on the number of edges,
    /// `W` can be an integer type and the weights of all edges can be set to `1`.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedTree;
    /// type Tree = FixedTree<i32, false>;
    ///
    /// let tree = Tree::try_from((5, [(0, 1, 1), (1, 2, 1), (1, 3, 1), (2, 4, 1)])).unwrap();
    /// let diameter = tree.diameter();
    /// assert_eq!(diameter.num_vertexes(), 4);
    /// assert_eq!(diameter.cost(), 3);
    ///
    /// // change (1, 3, 1) to (1, 3, 10)
    /// let tree = Tree::try_from((5, [(0, 1, 1), (1, 2, 1), (1, 3, 10), (2, 4, 1)])).unwrap();
    /// let diameter = tree.diameter();
    /// assert_eq!(diameter.num_vertexes(), 4);
    /// assert_eq!(diameter.cost(), 12);
    /// ```
    pub fn diameter(&self) -> Diameter<W> {
        let dist = self.path(0);
        let src = (0..self.num_vertexes())
            .max_by_key(|&i| dist.cost(i))
            .unwrap();
        let dist = self.path(src);
        let dst = (0..self.num_vertexes())
            .max_by_key(|&i| dist.cost(i))
            .unwrap();

        let (cost, path) = dist.path(dst).unwrap();
        Diameter { cost, path }
    }
}
