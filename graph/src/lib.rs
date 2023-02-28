mod bellman_ford;
mod cycle_detect;
mod dijkstra;
mod error;
mod graph_inner;
mod graphlike;
mod lca;
mod low_link;
mod nth_ancestor;
mod scc;
mod spanning_tree;
mod topological_sort;
mod tree;
mod warshall_floyd;

pub use bellman_ford::*;
pub use cycle_detect::*;
pub use dijkstra::*;
pub use error::*;
pub use graph_inner::*;
pub use graphlike::*;
pub use lca::*;
pub use low_link::*;
pub use nth_ancestor::*;
pub use scc::*;
pub use spanning_tree::*;
pub use topological_sort::*;
pub use tree::*;
pub use warshall_floyd::*;

pub trait Direction: Clone {
    fn is_directed() -> bool;
}
#[derive(Debug, Clone, std::marker::Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum UnDirected {}
impl Direction for UnDirected {
    fn is_directed() -> bool { false }
}
#[derive(Debug, Clone, std::marker::Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Directed {}
impl Direction for Directed {
    fn is_directed() -> bool { true }
}

#[derive(Debug, Clone, std::marker::Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Edge {
    pub to: usize,
    pub weight: i64,
}

pub struct Neighbors<'a> {
    inner: Box<dyn Iterator<Item = &'a usize> + 'a>,
}

impl<'a> Iterator for Neighbors<'a> {
    type Item = &'a usize;
    fn next(&mut self) -> Option<Self::Item> { self.inner.next() }
}

pub struct Edges<'a> {
    inner: Box<dyn Iterator<Item = (&'a usize, &'a i64)> + 'a>,
}

impl<'a> Iterator for Edges<'a> {
    type Item = (&'a usize, &'a i64);
    fn next(&mut self) -> Option<Self::Item> { self.inner.next() }
}

pub struct EdgesMut<'a> {
    inner: Box<dyn Iterator<Item = (&'a usize, &'a mut i64)> + 'a>,
}

impl<'a> Iterator for EdgesMut<'a> {
    type Item = (&'a usize, &'a mut i64);
    fn next(&mut self) -> Option<Self::Item> { self.inner.next() }
}

#[cfg(test)]
mod tests {
    use super::{bellman_ford, dijkstra_heap, dijkstra_v2, low_link, scc, topological_sort, warshall_floyd, DirectedGraph, UnDirectedGraph};
    use std::i64::MAX;

    #[test]
    fn graph_test() {
        // 9     1 --> 8 --> 4 --> 6     (0, 1, 3)           , (1, 8, 5)
        // ^     ^     |     |           (2, 0, 1), (2, 5, 9), (3, 0, 7), (3, 9, 3)
        // |     |     v     v           (4, 5, 4), (4, 6, 2),
        // 3 --> 0 <-- 2 --> 5           (7, 0, 8)           , (8, 2, 6), (8, 4, 1)
        //       ^
        //       |
        //       7
        let weighted_edges = vec![(0, 1, 3), (1, 8, 5), (2, 0, 1), (2, 5, 9), (3, 0, 7), (3, 9, 3), (4, 6, 2), (4, 5, 4), (7, 0, 8), (8, 2, 6), (8, 4, 1)];
        let dir: DirectedGraph = DirectedGraph::from_weighted_edges(10, weighted_edges);

        let dist = dijkstra_heap(0, &dir);
        assert_eq!(dist, vec![0, 3, 14, MAX, 9, 13, 11, MAX, 8, MAX]);

        let dist = dijkstra_v2(0, &dir);
        assert_eq!(dist, vec![0, 3, 14, MAX, 9, 13, 11, MAX, 8, MAX]);

        let dists = warshall_floyd(&dir);
        assert_eq!(
            dists,
            vec![
                vec![0, 3, 14, MAX, 9, 13, 11, MAX, 8, MAX],
                vec![12, 0, 11, MAX, 6, 10, 8, MAX, 5, MAX],
                vec![1, 4, 0, MAX, 10, 9, 12, MAX, 9, MAX],
                vec![7, 10, 21, 0, 16, 20, 18, MAX, 15, 3],
                vec![MAX, MAX, MAX, MAX, 0, 4, 2, MAX, MAX, MAX],
                vec![MAX, MAX, MAX, MAX, MAX, 0, MAX, MAX, MAX, MAX],
                vec![MAX, MAX, MAX, MAX, MAX, MAX, 0, MAX, MAX, MAX],
                vec![8, 11, 22, MAX, 17, 21, 19, 0, 16, MAX],
                vec![7, 10, 6, MAX, 1, 5, 3, MAX, 0, MAX],
                vec![MAX, MAX, MAX, MAX, MAX, MAX, MAX, MAX, MAX, 0]
            ]
        );

        let groups = scc(&dir);
        let groups = groups.into_iter().enumerate().fold(vec![0; 10], |mut v, (i, g)| {
            g.into_iter().for_each(|w| v[w] = i);
            v
        });
        assert_eq!(groups[0], groups[1]);
        assert_eq!(groups[0], groups[2]);
        assert_eq!(groups[0], groups[8]);
        assert_ne!(groups[0], groups[3]);
        assert_ne!(groups[0], groups[4]);
        assert!(groups[3] < groups[0]);
        assert!(groups[3] < groups[9]);
        assert!(groups[4] < groups[5]);
        assert!(groups[7] < groups[0]);

        // 0 --> 1 --> 2 --> 5 <-- 8    (0, 1, 1),              (1, 2, 2)
        //       ^     |     |     ^    (2, 3, -3), (2, 5, -6), (3, 4, 4)
        //       |     v     v     |    (4, 1, 1),              (5, 6, 3)
        //       4 <-- 3     6 --> 7    (6, 7, 7),              (7, 8, -9)
        //                              (8, 5, 4)
        let signed_weighted_edges = vec![(0, 1, 1), (1, 2, 2), (2, 3, -3), (2, 5, -6), (3, 4, 4), (4, 1, 1), (5, 6, 3), (6, 7, 7), (7, 8, -9), (8, 5, 4)];
        let dir: DirectedGraph = DirectedGraph::from_weighted_edges(9, signed_weighted_edges);

        let dist = bellman_ford(0, &dir).unwrap();
        assert_eq!(dist, vec![0, 1, 3, 0, 4, -3, 0, 7, -2]);

        // 0 --> 1 --> 2 --> 5 --> 8    (0, 1), (1, 2), (1, 4), (2, 3), (2, 5),
        //       |     |     |     ^    (4, 3), (5, 6), (5, 8), (6, 7), (7, 8)
        //       v     v     v     |
        //       4 --> 3     6 --> 7
        let edges = vec![(0, 1), (1, 2), (1, 4), (2, 3), (2, 5), (4, 3), (5, 6), (5, 8), (6, 7), (7, 8)];
        let dir: DirectedGraph = DirectedGraph::from_edges(9, edges);
        let list = topological_sort(&dir).unwrap().into_iter().enumerate().fold(vec![0; 9], |mut v, (i, s)| {
            v[s] = i;
            v
        });
        eprintln!("list: {:?}", list);
        assert!(list[0] < list[1]);
        assert!(list[1] < list[4]);
        assert!(list[2] < list[5]);
        assert!(list[0] < list[5]);
        assert!(list[5] < list[7]);

        // 0 --- 1 --- 2 --- 5 --- 8    (0, 1), (1, 2), (1, 4), (2, 3), (2, 5),
        //       |     |     |     |    (3, 4), (5, 6), (5, 8), (6, 7), (7, 8)
        //       4 --- 3     6 --- 7
        let edges = vec![(0, 1), (1, 2), (1, 4), (2, 3), (2, 5), (3, 4), (5, 6), (5, 8), (6, 7), (7, 8)];
        let undir: UnDirectedGraph = UnDirectedGraph::from_edges(9, edges);
        let mut links = low_link(&undir);
        links.sort();
        assert_eq!(links, vec![(0, 1), (2, 5)]);
    }

    use super::{lca, nth_ancestor, spanning_tree, Edge, UnDirectedTree};

    #[test]
    fn tree_test() {
        // +---+--+--+--+--+--+--+--+--+--+--+--+--+
        // |idx| 0| 1| 2| 3| 4| 5| 6| 7| 8| 9|10|11|
        // +---+--+--+--+--+--+--+--+--+--+--+--+--+
        // |par|NA| 0| 0| 1| 1| 2| 3| 4| 4| 5| 7| 9|
        // +---+--+--+--+--+--+--+--+--+--+--+--+--+
        let mut undir = UnDirectedTree::from_par_list(vec![std::usize::MAX, 0, 0, 1, 1, 2, 3, 4, 4, 5, 7, 9]).unwrap();

        let anc = nth_ancestor(&mut undir);
        assert_eq!(anc(6, 2), 1);
        assert_eq!(anc(1, 1), 0);
        assert_eq!(anc(3, 100000), std::usize::MAX);
        assert_eq!(anc(11, 3), 2);
        assert_eq!(anc(0, 1), std::usize::MAX);

        let lca = lca(&mut undir);
        assert_eq!(lca(10, 8), 4);
        assert_eq!(lca(11, 6), 0);
        assert_eq!(lca(2, 9), 2);
        assert_eq!(lca(0, 7), 0);
        assert_eq!(lca(3, 10), 1);

        // 9 --- 1 --- 8 --- 4 --- 6     (0, 1, 3), (0, 2, 1), (0, 3, 7), (0, 7, 8),
        // |     |     |     |           (1, 8, 5), (1, 9, 4),
        // |     |     |     |           (2, 5, 9), (2, 8, 6),
        // 3 --- 0 --- 2 --- 5           (3, 9, 3),
        //       |                       (4, 5, 4), (4, 6, 2), (4, 8, 1)
        //       |
        //       7
        let edges = vec![
            (0, 1, 3),
            (0, 2, 1),
            (0, 3, 7),
            (0, 7, 8),
            (1, 8, 5),
            (1, 9, 4),
            (2, 5, 9),
            (2, 8, 6),
            (3, 9, 3),
            (4, 5, 4),
            (4, 6, 2),
            (4, 8, 1),
        ];
        let undir = UnDirectedGraph::from_weighted_edges(10, edges);
        let tree = spanning_tree(&undir).unwrap();
        let set = (0..tree.size())
            .map(|i| {
                tree.graph[i]
                    .iter()
                    .map(|Edge { to, weight: _ }| (std::cmp::min(i, *to), std::cmp::max(i, *to)))
                    .collect::<Vec<(_, _)>>()
            })
            .flatten()
            .collect::<std::collections::BTreeSet<(_, _)>>()
            .iter()
            .map(|(f, t)| (*f, *t))
            .collect::<Vec<(_, _)>>();
        assert_eq!(set, vec![(0, 1), (0, 2), (0, 7), (1, 8), (1, 9), (3, 9), (4, 5), (4, 6), (4, 8)]);
    }

    #[test]
    #[should_panic]
    fn bellmanford_negative_cycle_detection() {
        // 0 --> 1 --> 2 --> 5 <-- 8    (0, 1, 1),              (1, 2, -5)
        //       ^     |     |     ^    (2, 3, -3), (2, 5, -6), (3, 4, 4)
        //       |     v     v     |    (4, 1, 1),              (5, 6, 3)
        //       4 <-- 3     6 --> 7    (6, 7, 7),              (7, 8, -9)
        //                              (8, 5, 4)
        let signed_weighted_edges = vec![(0, 1, 1), (1, 2, -5), (2, 3, -3), (2, 5, -6), (3, 4, 4), (4, 1, 1), (5, 6, 3), (6, 7, 7), (7, 8, -9), (8, 5, 4)];
        let dir: DirectedGraph = DirectedGraph::from_weighted_edges(9, signed_weighted_edges);

        // Panic!!!
        let _ = bellman_ford(0, &dir).unwrap();
    }

    #[test]
    #[should_panic]
    fn topologicalsort_cycle_detection() {
        // This graph has tow cycles.
        // 0 --> 1 --> 2 --> 5 <-- 8    (0, 1, 1),              (1, 2, -5)
        //       ^     |     |     ^    (2, 3, -3), (2, 5, -6), (3, 4, 4)
        //       |     v     v     |    (4, 1, 1),              (5, 6, 3)
        //       4 <-- 3     6 --> 7    (6, 7, 7),              (7, 8, -9)
        //                              (8, 5, 4)
        let signed_weighted_edges = vec![(0, 1, 1), (1, 2, -5), (2, 3, -3), (2, 5, -6), (3, 4, 4), (4, 1, 1), (5, 6, 3), (6, 7, 7), (7, 8, -9), (8, 5, 4)];
        let dir: DirectedGraph = DirectedGraph::from_weighted_edges(9, signed_weighted_edges);

        // Panic!!!
        let _ = topological_sort(&dir).unwrap();
    }

    #[test]
    #[should_panic]
    fn gen_invalid_tree_gen() {
        // Forget to fix to 0-index.
        // 10    2     9 --- 6 --- 7     (1, 2, 3), (1, 3, 1), (1, 5, 7), (1, 8, 8),
        // |     |           |           (3, 4, 9),
        // |     |           |           (4, 6, 3),
        // 5 --- 1 --- 3 --- 4           (5, 10, 4),
        //       |                       (6, 7, 4), (6, 9, 1)
        //       |
        //       8
        let edges = vec![(1, 2, 3), (1, 3, 1), (1, 5, 7), (1, 8, 8), (3, 4, 9), (4, 6, 3), (5, 10, 4), (6, 7, 4), (6, 9, 1)];

        // Panic!!!
        let _ = UnDirectedTree::from_weighted_edges(edges).unwrap();
    }
}
