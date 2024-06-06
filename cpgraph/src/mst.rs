use std::{cmp::Reverse, collections::BTreeMap};

use unionfind::UnionFind;

use crate::FixedGraph;

impl<W: Clone + Ord> FixedGraph<W, false> {
    /// Return the minimum spanning tree of this graph.  
    /// If such tree cannot be constructed, return `None`.
    ///
    /// The indexes on the edges are inherited in their original one.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedGraph;
    /// type Graph = FixedGraph<i32, false>;
    ///
    /// let graph = Graph::from((5, [(0, 1, 1), (0, 2, 2), (1, 2, 3), (2, 3, 4), (3, 4, 5)]));
    /// let mut mst_edges = graph.minimum_spanning_tree()
    ///     .unwrap()
    ///     .edges_all()
    ///     .filter_map(|e| (e.from() < e.to()).then_some((e.from(), e.to(), *e.weight())))
    ///     .collect::<Vec<_>>();
    ///
    /// mst_edges.sort();
    /// assert_eq!(mst_edges, vec![(0, 1, 1), (0, 2, 2), (2, 3, 4), (3, 4, 5)]);
    /// ```
    pub fn minimum_spanning_tree(&self) -> Option<FixedGraph<W, false>> {
        let mut edges = self
            .edges_all()
            .map(|e| (e.from(), e.to(), e.index(), e.weight().clone()))
            .collect::<Vec<_>>();
        edges.sort_unstable_by_key(|e| Reverse((e.3.clone(), e.2)));
        edges.dedup_by_key(|e| e.2);

        let mut uf = UnionFind::new(self.num_vertexes());
        let mut new = vec![];
        while let Some((from, to, index, w)) = edges.pop() {
            if uf.merge(from, to) {
                new.push((index as u32, from as u32, to as u32, w));
            }
        }

        let r = uf.root(0);
        (0..self.num_vertexes())
            .all(|i| uf.root(i) == r)
            .then(|| Self::from_edges_with_index(new))
    }
}

/// Perform 'Manhattan MST'.  
/// Returned items of `Vec` represent `(weight, from, to)`. These do not include edges not included in the MST.  
/// Input items represent the coordinates `(x, y)`.
///
/// https://hitonanode.github.io/cplib-cpp/graph/manhattan_mst.hpp
///
/// # Examples
/// ```rust
/// use cpgraph::manhattan_minimum_spanning_tree;
/// let edges = manhattan_minimum_spanning_tree(&[(3, 8), (4, 9), (2, 1), (10, 5), (4, 9), (2, 0)]);
/// let mut edges = edges.into_iter().map(|e| (e.1.min(e.2), e.1.max(e.2))).collect::<Vec<_>>();
/// edges.sort();
///
/// assert_eq!(edges, vec![(0, 1), (0, 2), (0, 3), (1, 4), (2, 5)]);
/// ```
pub fn manhattan_minimum_spanning_tree(xy: &[(i64, i64)]) -> Vec<(i64, usize, usize)> {
    let (mut xs, mut ys) = xy.iter().cloned().unzip::<i64, i64, Vec<i64>, Vec<i64>>();
    let n = xy.len();
    let mut idx = (0..n).collect::<Vec<_>>();
    let mut res: Vec<(i64, usize, usize)> = vec![];
    for _ in 0..2 {
        for _ in 0..2 {
            idx.sort_unstable_by_key(|&i| xs[i] + ys[i]);
            let mut sweep = BTreeMap::new();
            for &i in &idx {
                while let Some((&k, &j)) = sweep.range(-ys[i]..).next() {
                    if xs[i] - xs[j] < ys[i] - ys[j] {
                        break;
                    }
                    res.push((i64::abs(xs[i] - xs[j]) + i64::abs(ys[i] - ys[j]), i, j));
                    sweep.remove(&k);
                }
                sweep.insert(-ys[i], i);
            }
            (xs, ys) = (ys, xs);
        }
        xs.iter_mut().for_each(|x| *x = -*x);
    }

    res.sort_unstable();

    let mut uf = UnionFind::new(n);
    res.into_iter().filter(|e| uf.merge(e.1, e.2)).collect()
}
