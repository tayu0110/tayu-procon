use std::fmt::Debug;

use crate::FixedGraph;

impl<W: Clone + Debug, const DIR: bool> FixedGraph<W, DIR> {
    /// Check if this graph has some cycles.  
    /// If a cycle is detected, return one of them as `(vertexes, edges)`.  
    /// If not detected, return `None`.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedGraph;
    /// type Graph = FixedGraph<(), false>;
    ///
    /// let graph = Graph::from((6, [(0, 2), (0, 3), (4, 2), (3, 1), (2, 1), (2, 5)]));
    /// let (vertexes, edges) = graph.cycle_detect().unwrap();
    ///
    /// assert_eq!(vertexes.len(), edges.len());
    ///
    /// // This is one of the cycles.
    /// // There may be other cycles.
    /// assert_eq!(vertexes, vec![0, 2, 1, 3]);
    /// assert_eq!(edges, vec![0, 4, 3, 1]);
    /// ```
    pub fn cycle_detect(&self) -> Option<(Vec<usize>, Vec<usize>)> {
        // 0: not reached, 1: pending, 2: reached
        fn dfs<W: Clone + Debug, const DIR: bool>(
            now: usize,
            prev: usize,
            state: &mut [u8],
            graph: &FixedGraph<W, DIR>,
            rv: &mut Vec<usize>,
            re: &mut Vec<usize>,
        ) -> Option<usize> {
            if state[now] == 1 {
                return Some(now);
            }
            state[now] = 1;

            for edge in graph.edges(now) {
                if edge.index() == prev || state[edge.to()] == 2 {
                    continue;
                }

                if let Some(end) = dfs(edge.to(), edge.index(), state, graph, rv, re) {
                    if end < usize::MAX {
                        rv.push(now);
                        re.push(edge.index());
                    }
                    if end == now {
                        return Some(usize::MAX);
                    } else {
                        return Some(end);
                    }
                }
            }

            state[now] = 2;
            None
        }

        let mut state = vec![0; self.vertexes.len()];
        let mut rv = vec![];
        let mut re = vec![];
        for i in 0..self.vertexes.len() {
            if state[i] == 0 && dfs(i, usize::MAX, &mut state, self, &mut rv, &mut re).is_some() {
                break;
            }
        }

        (!re.is_empty()).then(|| {
            rv.reverse();
            re.reverse();
            (rv, re)
        })
    }
}
