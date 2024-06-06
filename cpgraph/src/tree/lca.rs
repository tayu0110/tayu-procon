use std::cmp::min_by_key;

use crate::FixedTree;

use super::euler_tour::EulerTour;

impl<W: Clone> FixedTree<W, false> {
    /// Construct the closure that finds Lowest Common Ancestor of the specified vertex pair on this tree.
    ///
    /// # Panics
    /// - `root < self.num_vertexes()` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedTree;
    /// type Tree = FixedTree<(), false>;
    ///
    /// let tree = Tree::try_from((8, [(0, 1), (0, 2), (1, 3), (2, 4), (2, 5), (4, 6), (6, 7)])).unwrap();
    /// let lca = tree.lca(0);
    ///
    /// assert_eq!(lca(3, 5), 0);
    /// assert_eq!(lca(5, 7), 2);
    /// assert_eq!(lca(6, 7), 6);
    /// assert_eq!(lca(0, 0), 0);
    /// ```
    pub fn lca(&self, root: usize) -> impl Fn(usize, usize) -> usize {
        assert!(root < self.num_vertexes());
        let EulerTour { vertexes, edge_indices: _, level } = self.euler_tour(root);
        let len = vertexes.len();
        let tr = len.next_power_of_two().trailing_zeros() as usize;
        let mut table = vec![vec![0; len]];
        let mut pos = vec![usize::MAX; self.num_vertexes()];
        for (i, &v) in vertexes.iter().enumerate() {
            table[0][i] = v;
            pos[v as usize] = pos[v as usize].min(i);
        }

        for i in 0..tr.saturating_sub(1) {
            let mut new = vec![u32::MAX; len];
            for j in (0..len).take_while(|&j| j + (1 << i) < len) {
                new[j] = min_by_key(table[i][j], table[i][j + (1 << i)], |&i| {
                    *level.get(i as usize).unwrap_or(&u32::MAX)
                });
            }
            table.push(new);
        }

        move |u: usize, v: usize| -> usize {
            if u == v {
                return u;
            }
            let (u, v) = (pos[u].min(pos[v]), pos[u].max(pos[v]));
            let d = (v - u + 1).next_power_of_two() >> 1;
            let tr = d.trailing_zeros() as usize;
            min_by_key(table[tr][u], table[tr][v - d], |&i| {
                *level.get(i as usize).unwrap_or(&u32::MAX)
            }) as usize
        }
    }
}
