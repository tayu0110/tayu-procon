use crate::FixedGraph;

fn dfs<W: Clone>(
    now: usize,
    used: &mut [bool],
    order: &mut Vec<usize>,
    graph: &FixedGraph<W, true>,
) {
    used[now] = true;
    for e in graph.edges(now) {
        if !used[e.to()] {
            dfs(e.to(), used, order, graph);
        }
    }
    order.push(now);
}

fn rdfs<W: Clone>(
    now: usize,
    group: i32,
    groups: &mut [i32],
    list: &mut Vec<usize>,
    graph: &FixedGraph<W, true>,
) {
    groups[now] = group;
    for e in graph.edges(now) {
        if groups[e.to()] < 0 {
            rdfs(e.to(), group, groups, list, graph);
        }
    }
    list.push(now);
}

impl<W: Clone> FixedGraph<W, true> {
    /// Perform Strongly Connected Component Decomposition of a directed graph by Kosaraju's algorithm.  
    /// The decomposed strongly connected components are ordered topologically and returned as two-dimensional vectors.  
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedGraph;
    /// type Graph = FixedGraph<(), true>;
    ///
    /// let graph = Graph::from((6, [(1, 4), (5, 2), (3, 0), (5, 5), (4, 1), (0, 3), (4, 2)]));
    /// let mut scc = graph.scc();
    /// scc.sort();
    ///
    /// assert_eq!(scc, vec![vec![2], vec![3, 0], vec![4, 1], vec![5]]);
    /// ```
    pub fn scc(&self) -> Vec<Vec<usize>> {
        let rg = FixedGraph::from((
            self.num_vertexes(),
            (0..self.num_vertexes()).flat_map(|i| self.edges(i).map(move |e| (e.to(), i, ()))),
        ));

        let mut used = vec![false; self.num_vertexes()];
        let mut order = vec![];
        for start in 0..self.num_vertexes() {
            if !used[start] {
                dfs(start, &mut used, &mut order, self);
            }
        }

        let mut group = 0;
        let mut groups = vec![-1; self.num_vertexes()];
        let mut res = vec![];
        while let Some(now) = order.pop() {
            if groups[now] < 0 {
                let mut list = vec![];
                rdfs(now, group, &mut groups, &mut list, &rg);
                group += 1;
                res.push(list);
            }
        }

        res
    }
}
