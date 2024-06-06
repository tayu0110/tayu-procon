use std::{cmp::Reverse, collections::BinaryHeap, ops::Add};

use crate::FixedGraph;

impl<W, const DIR: bool> FixedGraph<W, DIR>
where
    W: Clone + Default + Add<W, Output = W> + Ord,
{
    /// Return the path and cost between `src` and `dst`.
    ///
    /// # Constraint
    /// - For graphs with edges with negative weights, this method does not work correctly.
    ///
    /// # Panics
    /// - Both `src < self.num_vertexes()` and `dst < self.num_vertexes()` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedGraph;
    /// type Graph = FixedGraph<i32, true>;
    ///
    /// let graph = Graph::from((5, [(0, 3, 5), (0, 4, 3), (2, 4, 2), (4, 3, 10), (4, 0, 7), (2, 1, 5), (1, 0, 1)]));
    /// let (weight, path) = graph.shortest_path(2, 3).unwrap();
    ///
    /// assert_eq!(weight, 11);
    /// assert_eq!(path, vec![2, 1, 0, 3]);
    /// ```
    pub fn shortest_path(&self, src: usize, dst: usize) -> Option<(W, Vec<usize>)> {
        assert!(src < self.num_vertexes() && dst < self.num_vertexes());
        let mut nt = BinaryHeap::new();
        nt.push(Reverse((W::default(), src, src)));

        let mut prev = vec![usize::MAX; self.num_vertexes()];
        while let Some(Reverse((w, now, p))) = nt.pop() {
            if prev[now] != usize::MAX {
                continue;
            }
            prev[now] = p;

            if now == dst {
                let mut path = vec![];
                let mut now = now;
                while prev[now] != now {
                    path.push(now);
                    now = prev[now];
                }
                path.push(now);
                path.reverse();
                return Some((w, path));
            }
            for e in self.edges(now) {
                if prev[e.to()] == usize::MAX {
                    nt.push(Reverse((w.clone() + e.weight().clone(), e.to(), now)));
                }
            }
        }

        None
    }
}
