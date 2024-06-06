use std::collections::{HashSet, VecDeque};

use crate::FixedGraph;

/// Return `(ord, low)`.
fn low_link<W: Clone>(graph: &FixedGraph<W, false>) -> (Vec<u32>, Vec<u32>) {
    let mut ord = vec![u32::MAX; graph.num_vertexes()];
    let mut low = ord.clone();

    fn dfs<W: Clone>(
        now: usize,
        prev: usize,
        cnt: u32,
        ord: &mut [u32],
        low: &mut [u32],
        graph: &FixedGraph<W, false>,
    ) -> u32 {
        ord[now] = cnt;
        low[now] = ord[now];

        let mut next = cnt + 1;
        for e in graph.edges(now) {
            if e.index() != prev {
                if ord[e.to()] == u32::MAX {
                    next = dfs(e.to(), e.index(), next, ord, low, graph);
                    low[now] = low[now].min(low[e.to()]);
                } else {
                    low[now] = low[now].min(ord[e.to()]);
                }
            }
        }

        next
    }

    for i in 0..graph.num_vertexes() {
        if ord[i] == u32::MAX {
            dfs(i, usize::MAX, 0, &mut ord, &mut low, graph);
        }
    }
    (ord, low)
}

impl<W: Clone> FixedGraph<W, false> {
    /// Detect all bridges in the graph.  
    /// In the case of an undirected graph, only edges are returned such that the start point is always indexed less than the end point.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedGraph;
    /// type Graph = FixedGraph<(), false>;
    ///
    /// let graph = Graph::from((8, [(0, 1), (0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (4, 5), (5, 6), (6, 7)]));
    /// let mut bridges = graph.bridges().collect::<Vec<_>>();
    /// bridges.sort();
    ///
    /// // all tuples always satisfies `bridge.0 < bridge.1`.
    /// assert_eq!(bridges, vec![(2, 3), (5, 6), (6, 7)]);
    /// ```
    pub fn bridges(&self) -> impl Iterator<Item = (usize, usize)> + '_ {
        let (ord, low) = low_link(self);
        self.edges_all()
            .filter_map(move |e| (ord[e.from()] < low[e.to()]).then_some((e.from(), e.to())))
    }

    /// Detect all articulation points.  
    /// A articulation point is a point that can be deleted to disconnect the graph.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedGraph;
    /// type Graph = FixedGraph<(), false>;
    ///
    /// let graph = Graph::from((8, [(0, 1), (0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (4, 5), (5, 6), (6, 7)]));
    /// let mut articulation_points = graph.articulation_points().collect::<Vec<_>>();
    /// articulation_points.sort();
    ///
    /// assert_eq!(articulation_points, vec![2, 3, 5, 6]);
    /// ```
    pub fn articulation_points(&self) -> impl Iterator<Item = usize> + '_ {
        let (ord, low) = low_link(self);
        (0..self.num_vertexes()).filter(move |&i| {
            if ord[i] == 0 {
                self.edges(i).filter(|e| low[e.to()] != 0).count() > 1
            } else {
                self.edges(i)
                    .any(|e| ord[e.to()] > ord[i] && ord[i] <= low[e.to()])
            }
        })
    }

    /// Returns a list of each connected component after the graph is partitioned by bridges.
    ///
    /// The order of vertexes and connected components has no meaning.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedGraph;
    /// type Graph = FixedGraph<(), false>;
    ///
    /// let graph = Graph::from((8, [(0, 1), (0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (4, 5), (5, 6), (6, 7)]));
    /// let mut components = graph.two_edge_connected_components();
    /// components.iter_mut().for_each(|c| c.sort());
    /// components.sort();
    ///
    /// // (2, 3), (5, 6) and (6, 7) are bridges.
    /// assert_eq!(components, vec![vec![0, 1, 2], vec![3, 4, 5], vec![6], vec![7]]);
    /// ```
    pub fn two_edge_connected_components(&self) -> Vec<Vec<usize>> {
        let bridge = self
            .bridges()
            .map(|(i, j)| (i.min(j), i.max(j)))
            .collect::<HashSet<_>>();

        let mut group = vec![-1; self.num_vertexes()];
        let mut cnt = 0;
        for i in 0..self.num_vertexes() {
            if group[i] < 0 {
                let mut nt = VecDeque::from([i]);
                group[i] = cnt;
                while let Some(now) = nt.pop_front() {
                    for e in self.edges(now) {
                        if group[e.to()] < 0
                            && !bridge.contains(&(now.min(e.to()), now.max(e.to())))
                        {
                            group[e.to()] = cnt;
                            nt.push_back(e.to());
                        }
                    }
                }

                cnt += 1;
            }
        }

        let mut res = vec![vec![]; cnt as usize];
        for (i, g) in group.into_iter().enumerate() {
            res[g as usize].push(i);
        }

        res
    }

    /// Returns a list of each connected component after the graph is partitioned by articulation points.  
    /// reference : https://kokiymgch.hatenablog.com/entry/2018/03/21/152148
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedGraph;
    /// type Graph = FixedGraph<(), false>;
    ///
    /// let graph = Graph::from((8, [(0, 1), (0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (4, 5), (5, 6), (6, 7)]));
    /// let mut components = graph.biconnected_components();
    /// components.iter_mut().for_each(|c| c.sort());
    /// components.sort();
    ///
    /// // 2, 3, 5 and 6 are articulation points.
    /// assert_eq!(components, vec![vec![0, 1, 2], vec![2, 3], vec![3, 4, 5], vec![5, 6], vec![6, 7]]);
    /// ```
    pub fn biconnected_components(&self) -> Vec<Vec<usize>> {
        let (ord, low) = low_link(self);

        let mut res = vec![];
        let mut edges = vec![];
        let mut reached = vec![false; self.num_vertexes()];
        for i in 0..self.num_vertexes() {
            if ord[i] == 0 {
                if self.edges(i).len() == 0 {
                    res.push(vec![i]);
                    continue;
                }
                let mut stack = vec![(i, usize::MAX, 0usize)];
                'b: while let Some((now, prev, e)) = stack.pop() {
                    reached[now] = true;
                    if let Some(e) = self
                        .nth_edge(now, e.wrapping_sub(1))
                        .filter(|e| ord[now] <= low[e.to()])
                    {
                        let mut buf = vec![];
                        while let Some((u, v)) = edges.pop() {
                            buf.push(u);
                            buf.push(v);
                            if (u, v) == (now.min(e.to()), now.max(e.to())) {
                                break;
                            }
                        }
                        buf.sort_unstable();
                        buf.dedup();
                        res.push(buf);
                    }

                    for (j, e) in self
                        .edges(now)
                        .enumerate()
                        .skip(e)
                        .filter(|e| e.1.to() != prev)
                    {
                        if ord[now] > ord[e.to()] || !reached[e.to()] {
                            edges.push((now.min(e.to()), now.max(e.to())));
                        }
                        if !reached[e.to()] {
                            stack.push((now, prev, j + 1));
                            stack.push((e.to(), now, 0));
                            continue 'b;
                        }
                    }
                }
            }
        }

        res
    }
}
