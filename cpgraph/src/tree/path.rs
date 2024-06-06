use crate::{FixedTree, SaturatingOps};

pub struct Path<W> {
    prev: Vec<usize>,
    dist: Vec<W>,
}

impl<W: Clone + Ord + SaturatingOps> Path<W> {
    /// Return the path between `src` and `to`.  
    /// The cost of this path is also returned.
    ///
    /// If such paths are not found, return `None`.
    pub fn path(&self, to: usize) -> Option<(W, Vec<usize>)> {
        (self.dist[to] < W::MAX).then(|| {
            let w = self.dist[to].clone();
            let mut path = vec![];
            let mut now = to;
            while self.prev[now] != now {
                path.push(now);
                now = self.prev[now];
            }
            path.push(now);
            path.reverse();
            (w, path)
        })
    }

    /// Return the cost of the path between `src` and `to`.  
    /// If there are no path between `src` and `to`, return `None`.
    pub fn cost(&self, to: usize) -> Option<W> {
        (self.dist[to] < W::MAX).then(|| self.dist[to].clone())
    }
}

impl<W, const DIR: bool> FixedTree<W, DIR>
where
    W: Clone + Default + SaturatingOps + Ord,
{
    /// Find paths and costs from `src` to reachable vertexes.  
    /// The information of paths and costs can be accessed from returned `Path`.
    ///
    /// # Panics
    /// - `src < self.num_vertexes()` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedTree;
    /// type Tree = FixedTree<i32, false>;
    ///
    /// let tree = Tree::try_from((5, [(0, 1, 1), (0, 2, 2), (1, 3, 3), (3, 4, 4)])).unwrap();
    /// let path = tree.path(0);
    ///
    /// assert_eq!(path.path(4), Some((8, vec![0, 1, 3, 4])));
    /// assert_eq!(path.cost(2), Some(2));
    /// ```
    pub fn path(&self, src: usize) -> Path<W> {
        assert!(src < self.num_vertexes());
        let mut dist = vec![W::MAX; self.num_vertexes()];
        let mut prev = vec![usize::MAX; self.num_vertexes()];
        dist[src] = W::default();
        prev[src] = src;

        let mut stack = vec![src];
        while let Some(now) = stack.pop() {
            for e in self.edges(now) {
                if prev[e.to()] == usize::MAX {
                    dist[e.to()] = dist[now].saturating_add(e.weight());
                    prev[e.to()] = now;
                    stack.push(e.to());
                }
            }
        }

        Path { prev, dist }
    }
}
