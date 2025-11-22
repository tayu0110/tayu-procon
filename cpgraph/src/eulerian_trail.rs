use crate::FixedGraph;

// reference : https://kokiymgch.hatenablog.com/entry/2017/12/07/193238
fn eulerian_trail_core<W: Clone, const DIR: bool>(
    base: &FixedGraph<W, DIR>,
    src: usize,
) -> Option<(Vec<usize>, Vec<usize>)> {
    let mut used = vec![false; base.num_edges()];
    let mut graph = vec![vec![]; base.num_vertexes()];
    for i in 0..base.num_vertexes() {
        for e in base.edges(i) {
            graph[e.to()].push((i, e.index()));
        }
    }

    let mut vertexes = vec![];
    let mut edges = vec![];
    fn dfs(
        now: usize,
        pe: usize,
        vertexes: &mut Vec<usize>,
        edges: &mut Vec<usize>,
        used: &mut [bool],
        graph: &mut [Vec<(usize, usize)>],
    ) {
        while let Some((to, index)) = graph[now].pop() {
            if used[index] {
                continue;
            }
            used[index] = true;

            dfs(to, index, vertexes, edges, used, graph);
        }
        vertexes.push(now);
        if pe != usize::MAX {
            edges.push(pe);
        }
    }

    dfs(
        src,
        usize::MAX,
        &mut vertexes,
        &mut edges,
        &mut used,
        &mut graph,
    );
    (0..graph.len()).all(|i| graph[i].is_empty()).then(|| {
        if vertexes.is_empty() {
            vertexes.push(0);
        }
        (vertexes, edges)
    })
}

impl<W: Clone> FixedGraph<W, false> {
    /// Find an Eulerian Trail on this graph and return as `(vertexes, edges)`.  
    /// If not found, return `None`.
    ///
    /// The Nth edge always connects between Nth vertex and (N+1)th vertex.  
    /// And `edges.len()` is always equal to `self.num_edges()`.
    ///
    /// It works correctly even if it contains multiple edges and self-loops.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedGraph;
    /// type Graph = FixedGraph<(), false>;
    ///
    /// let graph = Graph::from((5, [(0, 1), (0, 2), (1, 1), (1, 3), (2, 3), (2, 3), (2, 4), (3, 4)]));
    /// let (vertexes, mut edges) = graph.eulerian_trail().unwrap();
    /// assert_eq!(edges.len(), graph.num_edges());
    /// assert_eq!(edges.len() + 1, vertexes.len());
    ///
    /// // Every edge appears on the trail exactly once.
    /// edges.sort();
    /// edges.dedup();
    /// assert_eq!(edges.len(), graph.num_edges());
    /// ```
    pub fn eulerian_trail(&self) -> Option<(Vec<usize>, Vec<usize>)> {
        let sd = (0..self.num_vertexes())
            .filter(|v| self.edges(*v).len() % 2 == 1)
            .collect::<Vec<_>>();
        (sd.is_empty() || sd.len() == 2).then(|| {
            let s = (0..self.num_vertexes())
                .find(|&i| self.edges(i).len() > 0)
                .unwrap_or_default();
            eulerian_trail_core(self, sd.first().cloned().unwrap_or(s))
        })?
    }
}

impl<W: Clone> FixedGraph<W, true> {
    /// Find an Eulerian Trail on this graph and return as `(vertexes, edges)`.  
    /// If not found, return `None`.
    ///
    /// The Nth edge always connects between Nth vertex and (N+1)th vertex.  
    /// And `edges.len()` is always equal to `self.num_edges()`.
    ///
    /// It works correctly even if it contains multiple edges and self-loops.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedGraph;
    /// type Graph = FixedGraph<(), true>;
    ///
    /// let graph = Graph::from((5, [(0, 1), (0, 2), (1, 1), (1, 3), (2, 3), (2, 3), (3, 0), (3, 4), (4, 2)]));
    /// let (vertexes, mut edges) = graph.eulerian_trail().unwrap();
    /// assert_eq!(edges.len(), graph.num_edges());
    /// assert_eq!(edges.len() + 1, vertexes.len());
    ///
    /// // Every edge appears on the trail exactly once.
    /// edges.sort();
    /// edges.dedup();
    /// assert_eq!(edges.len(), graph.num_edges());
    /// ```
    pub fn eulerian_trail(&self) -> Option<(Vec<usize>, Vec<usize>)> {
        let mut ins = vec![0u32; self.num_vertexes()];
        for i in 0..self.num_vertexes() {
            for e in self.edges(i) {
                ins[e.to()] += 1;
            }
        }

        let sd = (0..self.num_vertexes())
            .filter_map(|i| {
                let d = ins[i].abs_diff(self.edges(i).len() as u32);
                (d > 0).then_some((i, d))
            })
            .collect::<Vec<_>>();

        ((sd.is_empty() || sd.len() == 2) && sd.iter().all(|v| v.1 == 1)).then(|| {
            if !sd.is_empty() {
                let (s, _) = sd[0];
                let f = ins[s] as usize + 1 == self.edges(s).len();
                eulerian_trail_core(self, sd[f as usize].0)
            } else {
                let s = (0..self.num_vertexes())
                    .find(|&i| self.edges(i).len() > 0)
                    .unwrap_or_default();
                eulerian_trail_core(self, s)
            }
        })?
    }
}
