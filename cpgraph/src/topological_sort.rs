use std::{cmp::Reverse, collections::BinaryHeap};

use crate::FixedGraph;

impl<W: Clone> FixedGraph<W, true> {
    /// Returns the topological sort of a directed graph.  
    /// If a cycle is detected, return `None`.
    ///
    /// It is guaranteed that the smallest topological sort in lexicographic order will be returned.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedGraph;
    /// type Graph = FixedGraph<(), true>;
    ///
    /// let graph = Graph::from((5, [(2, 1), (3, 4), (2, 4)]));
    /// let topo = graph.topological_sort().unwrap();
    /// assert_eq!(topo, vec![0, 2, 1, 3, 4]);
    /// ```
    pub fn topological_sort(&self) -> Option<Vec<usize>> {
        let mut res = vec![];
        let mut ins = vec![0; self.num_vertexes()];

        for now in 0..self.num_vertexes() {
            for e in self.edges(now) {
                ins[e.to()] += 1;
            }
        }

        let mut nt = ins
            .iter()
            .enumerate()
            .filter_map(|(i, &v)| (v == 0).then_some(Reverse(i)))
            .collect::<BinaryHeap<_>>();
        while let Some(Reverse(now)) = nt.pop() {
            if ins[now] < 0 {
                continue;
            }
            ins[now] = -1;
            res.push(now);

            for e in self.edges(now) {
                let to = e.to();
                if ins[to] > 0 {
                    ins[to] -= 1;
                    if ins[to] == 0 {
                        nt.push(Reverse(to));
                    }
                }
            }
        }

        (res.len() == self.num_vertexes()).then_some(res)
    }
}
