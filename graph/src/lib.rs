pub trait Direction: Clone {
    fn is_directed() -> bool;
}
#[derive(Debug, Clone, std::marker::Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum UnDirected {}
impl Direction for UnDirected {
    fn is_directed() -> bool {
        false
    }
}
#[derive(Debug, Clone, std::marker::Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Directed {}
impl Direction for Directed {
    fn is_directed() -> bool {
        true
    }
}

#[derive(Debug, Clone, std::marker::Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct Edge {
    pub to: usize,
    pub weight: i64,
}

pub type DirectedGraph = Graph<Directed>;
pub type UnDirectedGraph = Graph<UnDirected>;

#[derive(Debug, Clone)]
pub struct Graph<D: Direction> {
    size: usize,
    graph: Vec<Vec<Edge>>,
    _d: std::marker::PhantomData<D>,
}

impl<'a, D: Direction> Graph<D> {
    #[inline]
    pub fn new(size: usize) -> Self {
        Self {
            size,
            graph: vec![vec![]; size],
            _d: std::marker::PhantomData,
        }
    }

    #[inline]
    pub fn from_weighted_edges(size: usize, edges: Vec<(usize, usize, i64)>) -> Self {
        edges
            .into_iter()
            .fold(Self::new(size), |mut g, (from, to, weight)| {
                g.set_weighted_edge(from, to, weight);
                g
            })
    }

    #[inline]
    pub fn from_edges(size: usize, edges: Vec<(usize, usize)>) -> Self {
        edges
            .into_iter()
            .fold(Self::new(size), |mut g, (from, to)| {
                g.set_edge(from, to);
                g
            })
    }

    #[inline]
    pub fn set_weighted_edge(&mut self, from: usize, to: usize, weight: i64) {
        self.graph[from].push(Edge { to, weight });
        if !D::is_directed() && from != to {
            self.graph[to].push(Edge { to: from, weight });
        }
    }

    #[inline]
    pub fn set_edge(&mut self, from: usize, to: usize) {
        self.set_weighted_edge(from, to, 1)
    }

    #[inline]
    pub fn resize(&mut self, size: usize) {
        self.size = size;
        self.graph.resize(size, vec![]);
    }

    #[inline]
    pub fn neighbors(&'a self, index: usize) -> Neighbors<'a> {
        Neighbors {
            inner: self.graph[index].iter(),
        }
    }

    #[inline]
    pub fn edges(&'a self, index: usize) -> Edges<'a> {
        Edges {
            inner: self.graph[index].iter(),
        }
    }

    #[inline]
    pub fn edges_mut(&'a mut self, index: usize) -> EdgesMut<'a> {
        EdgesMut {
            inner: self.graph[index].iter_mut(),
        }
    }

    pub fn rev_graph(&self) -> Self {
        let mut graph = vec![vec![]; self.size];

        for from in 0..self.size {
            for Edge { to, weight } in &self.graph[from] {
                graph[*to].push(Edge {
                    to: from,
                    weight: *weight,
                });
            }
        }

        Self {
            size: self.size,
            graph,
            _d: std::marker::PhantomData,
        }
    }
}

impl<D: Direction> std::convert::From<Vec<(usize, usize)>> for Graph<D> {
    fn from(from: Vec<(usize, usize)>) -> Self {
        let mut graph = Graph::<D>::new(1 << 10);
        let mut max = 0;

        for (from, to) in from {
            max = std::cmp::max(max, std::cmp::max(from, to));
            if max >= graph.size {
                graph.resize(std::cmp::max(from, to).next_power_of_two());
            }

            graph.set_edge(from, to);
        }

        graph.resize(max + 1);

        graph
    }
}

impl<D: Direction> std::convert::From<Vec<(usize, usize, i64)>> for Graph<D> {
    fn from(from: Vec<(usize, usize, i64)>) -> Self {
        let mut graph = Graph::<D>::new(1 << 10);
        let mut max = 0;

        for (from, to, weight) in from {
            max = std::cmp::max(max, std::cmp::max(from, to));
            if max >= graph.size {
                graph.resize(std::cmp::max(from, to).next_power_of_two());
            }

            graph.set_weighted_edge(from, to, weight);
        }

        graph.resize(max + 1);

        graph
    }
}

impl<D: Direction> std::convert::From<Vec<Vec<usize>>> for Graph<D> {
    fn from(from: Vec<Vec<usize>>) -> Self {
        let size = from.len();
        let edges = if D::is_directed() {
            from.into_iter()
                .enumerate()
                .map(|(from, v)| v.into_iter().map(move |to| (from, to)))
                .flatten()
                .collect()
        } else {
            from.into_iter()
                .enumerate()
                .map(|(from, v)| {
                    v.into_iter()
                        .filter(move |to| from <= *to)
                        .map(move |to| (from, to))
                })
                .flatten()
                .collect()
        };

        Graph::<D>::from_edges(size, edges)
    }
}

impl<D: Direction> std::convert::From<Vec<Vec<(usize, i64)>>> for Graph<D> {
    fn from(from: Vec<Vec<(usize, i64)>>) -> Self {
        let size = from.len();
        let edges = if D::is_directed() {
            from.into_iter()
                .enumerate()
                .map(|(from, v)| v.into_iter().map(move |(to, weight)| (from, to, weight)))
                .flatten()
                .collect()
        } else {
            from.into_iter()
                .enumerate()
                .map(|(from, v)| {
                    v.into_iter()
                        .filter(move |(to, _)| from <= *to)
                        .map(move |(to, weight)| (from, to, weight))
                })
                .flatten()
                .collect()
        };

        Graph::<D>::from_weighted_edges(size, edges)
    }
}

pub struct Neighbors<'a> {
    inner: std::slice::Iter<'a, Edge>,
}

impl<'a> Iterator for Neighbors<'a> {
    type Item = &'a usize;
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|Edge { to, weight: _ }| to)
    }
}

pub struct Edges<'a> {
    inner: std::slice::Iter<'a, Edge>,
}

impl<'a> Iterator for Edges<'a> {
    type Item = (&'a usize, &'a i64);
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|Edge { to, weight }| (to, weight))
    }
}

pub struct EdgesMut<'a> {
    inner: std::slice::IterMut<'a, Edge>,
}

impl<'a> Iterator for EdgesMut<'a> {
    type Item = (&'a usize, &'a mut i64);
    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|Edge { to, weight }| (&*to, weight))
    }
}

/// Find the single starting point shortest path by Dijkstra's algorithm.  
/// The computational complexity is O(ElogV), where E is the number of edges and V is the number of vertices, because a BinaryHeap is used.  
/// If there is an unreachable vertex, the distance of that vertex is std::i64::MAX  
pub fn dijkstra_heap<D: Direction>(from: usize, graph: &Graph<D>) -> Vec<i64> {
    let mut res = vec![std::i64::MAX; graph.size];

    let mut nt = std::collections::BinaryHeap::new();
    nt.push(std::cmp::Reverse((0, from)));

    while let Some(std::cmp::Reverse((nd, now))) = nt.pop() {
        if res[now] != std::i64::MAX {
            continue;
        }
        res[now] = nd;

        for (to, weight) in graph.edges(now) {
            if res[*to] == std::i64::MAX {
                nt.push(std::cmp::Reverse((nd + *weight, *to)));
            }
        }
    }

    res
}

/// Find the single starting point shortest path by Dijkstra's algorithm.  
/// The computational complexity is O(V^2), where V is the number of vertices.  
/// If there is an unreachable vertex, the distance of that vertex is std::i64::MAX  
pub fn dijkstra_v2<D: Direction>(from: usize, graph: &Graph<D>) -> Vec<i64> {
    let mut res = vec![std::i64::MAX; graph.size];
    let mut checked = vec![false; graph.size];
    res[from] = 0;

    let mut now = from;
    for _ in 0..graph.size {
        checked[now] = true;
        for (to, weight) in graph.edges(now) {
            res[*to] = std::cmp::min(res[*to], res[now] + *weight);
        }
        let mut new = (std::i64::MAX, graph.size + 1);
        for next in 0..graph.size {
            if !checked[next] {
                new = std::cmp::min(new, (res[next], next));
            }
        }
        if new.0 == std::i64::MAX {
            break;
        }
        now = new.1;
    }

    res
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct NegativeCycleError;
impl std::fmt::Display for NegativeCycleError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "This graph has some negative cycles.")
    }
}
impl std::error::Error for NegativeCycleError {}

/// Find the single starting point shortest path by Bellman-Ford's algorithm.  
/// If the graph has negative cycle, return NegativeCycleError and the solution updated with std::i64::MIN for the cost of the vertices affected by the negative cycle.  
pub fn bellman_ford<D: Direction>(
    from: usize,
    graph: &Graph<D>,
) -> Result<Vec<i64>, (NegativeCycleError, Vec<i64>)> {
    const INF: i64 = std::i64::MAX;
    let mut res = vec![INF; graph.size];
    res[from] = 0;

    let mut negative_cycle = false;
    for i in 0..graph.size * 2 {
        let mut updated = false;
        for from in 0..graph.size {
            for (to, weight) in graph.edges(from) {
                if res[*to] > res[from] + *weight {
                    if i < graph.size - 1 {
                        res[*to] = res[from] + *weight;
                    } else {
                        res[*to] = std::i64::MIN;
                        negative_cycle = true;
                    }
                    updated = true;
                }
            }
        }
        if !updated {
            break;
        }
    }

    if negative_cycle {
        Err((NegativeCycleError, res))
    } else {
        Ok(res)
    }
}

pub fn warshall_floyd<D: Direction>(graph: &Graph<D>) -> Vec<Vec<i64>> {
    let mut res = vec![vec![std::i64::MAX; graph.size]; graph.size];

    for from in 0..graph.size {
        res[from][from] = 0;
        for (to, weight) in graph.edges(from) {
            res[from][*to] = *weight;
        }
    }

    for k in 0..graph.size {
        for i in 0..graph.size {
            for j in 0..graph.size {
                res[i][j] = std::cmp::min(res[i][j], res[i][k].saturating_add(res[k][j]));
            }
        }
    }

    res
}

/// Perform strongly connected component decomposition of a directed graph by Losaraju's algorithm.  
/// The decomposed strongly connected components are ordered topologically and returned as two-dimensional vectors.  
pub fn scc(graph: &Graph<Directed>) -> Vec<Vec<usize>> {
    let rev_graph = graph.rev_graph();

    let mut used = vec![false; graph.size];
    let mut order = vec![];
    for start in 0..graph.size {
        if !used[start] {
            dfs_for_scc(start, &mut used, &mut order, &graph);
        }
    }

    let mut group = 0;
    let mut groups = vec![-1; graph.size];
    let mut res = vec![];
    while let Some(now) = order.pop() {
        if groups[now] < 0 {
            let mut list = vec![];
            rdfs_for_scc(now, group, &mut groups, &mut list, &rev_graph);
            group += 1;
            res.push(list);
        }
    }

    res
}
fn dfs_for_scc(now: usize, used: &mut Vec<bool>, order: &mut Vec<usize>, graph: &Graph<Directed>) {
    used[now] = true;
    for Edge { to, weight: _ } in &graph.graph[now] {
        if !used[*to] {
            dfs_for_scc(*to, used, order, graph);
        }
    }
    order.push(now);
}
fn rdfs_for_scc(
    now: usize,
    group: i32,
    groups: &mut Vec<i32>,
    list: &mut Vec<usize>,
    graph: &Graph<Directed>,
) {
    groups[now] = group;
    for Edge { to, weight: _ } in &graph.graph[now] {
        if groups[*to] < 0 {
            rdfs_for_scc(*to, group, groups, list, graph);
        }
    }
    list.push(now);
}

/// Detect bridges in the graph.  
/// The detected bridges are returned as a list of tuples of vertices at both ends.  
/// The elements of a tuple are always placed with the directed edge source in front and destination behind.  
pub fn low_link<D: Direction>(graph: &Graph<D>) -> Vec<(usize, usize)> {
    let mut ord = vec![std::usize::MAX; graph.size];
    let mut low = vec![std::usize::MAX; graph.size];

    let mut next_ord = 0;
    let mut res = vec![];
    for start in 0..graph.size {
        if ord[start] == std::usize::MAX {
            next_ord = dfs_for_lowlink(
                start,
                std::usize::MAX,
                next_ord,
                &mut ord,
                &mut low,
                &mut res,
                &graph,
            );
        }
    }
    res
}
fn dfs_for_lowlink<D: Direction>(
    now: usize,
    par: usize,
    now_ord: usize,
    ord: &mut Vec<usize>,
    low: &mut Vec<usize>,
    res: &mut Vec<(usize, usize)>,
    graph: &Graph<D>,
) -> usize {
    ord[now] = now_ord;
    low[now] = ord[now];

    let mut next_ord = now_ord + 1;
    for Edge { to, weight: _ } in &graph.graph[now] {
        if ord[*to] == std::usize::MAX {
            next_ord = dfs_for_lowlink(*to, now, next_ord, ord, low, res, graph);
            low[now] = std::cmp::min(low[now], low[*to]);
            if ord[now] < low[*to] {
                res.push((now, *to));
            }
        }
        if *to != par {
            low[now] = std::cmp::min(low[now], ord[*to]);
        }
    }

    next_ord
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct CycleDetectionError;
impl std::fmt::Display for CycleDetectionError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Some Cycles are Detected.")
    }
}
impl std::error::Error for CycleDetectionError {}

/// Returns the topological sort of a directed graph.  
/// If a cycle is detected, a topological sort cannot be defined, so CycleDetectionError is returned.  
pub fn topological_sort(graph: &Graph<Directed>) -> Result<Vec<usize>, CycleDetectionError> {
    let mut res = vec![];
    let mut ins = vec![0; graph.size];

    for now in 0..graph.size {
        for Edge { to, weight: _ } in &graph.graph[now] {
            ins[*to] += 1;
        }
    }

    let mut nt = ins
        .iter()
        .enumerate()
        .filter(|(_, v)| **v == 0)
        .map(|(i, _)| i)
        .collect::<std::collections::VecDeque<_>>();
    while let Some(now) = nt.pop_front() {
        if ins[now] < 0 {
            continue;
        }
        ins[now] = -1;
        res.push(now);

        for Edge { to, weight: _ } in &graph.graph[now] {
            if ins[*to] > 0 {
                ins[*to] -= 1;
                if ins[*to] == 0 {
                    nt.push_back(*to);
                }
            }
        }
    }

    if res.len() < graph.size {
        Err(CycleDetectionError)
    } else {
        Ok(res)
    }
}

/// Detect cycles in a directed graph.
/// If a cycle is successfully detected, return a vertex list for one of cycles.
/// The vertex list is in topological order when one edge of the cycle is cut.
pub fn cycle_detect(graph: &Graph<Directed>) -> Option<Vec<usize>> {
    let size = graph.size;
    // 0: not reached, 1: pending, 2: reached
    let mut state = vec![0u8; size];

    for i in 0..size {
        if state[i] != 2 {
            let mut res = vec![];
            if let Some(_) = dfs_for_cycle_detect(i, &mut state, &mut res, &graph) {
                res.reverse();
                return Some(res);
            }
        }
    }

    None
}
fn dfs_for_cycle_detect(
    now: usize,
    state: &mut [u8],
    stack: &mut Vec<usize>,
    graph: &Graph<Directed>,
) -> Option<usize> {
    state[now] = 1;

    for to in graph.neighbors(now) {
        if state[*to] == 2 {
            continue;
        }
        if state[*to] == 1 {
            stack.push(now);
            return Some(*to);
        }

        if let Some(mut res) = dfs_for_cycle_detect(*to, state, stack, graph) {
            if res != std::usize::MAX {
                stack.push(now);
            }
            if res == now {
                res = std::usize::MAX;
            }
            return Some(res);
        }
    }

    state[now] = 2;
    None
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct InvalidTree;
impl std::fmt::Display for InvalidTree {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Invalid Tree")
    }
}
impl std::error::Error for InvalidTree {}

pub type DirectedTree = Tree<Directed>;
pub type UnDirectedTree = Tree<UnDirected>;

#[derive(Debug, Clone)]
pub struct Tree<D: Direction> {
    size: usize,
    root: usize,
    par: Vec<usize>,
    graph: Vec<Vec<Edge>>,
    _d: std::marker::PhantomData<D>,
}

impl<'a, D: Direction> Tree<D> {
    pub fn from_weighted_edges(edges: Vec<(usize, usize, i64)>) -> Result<Self, InvalidTree> {
        let size = edges.len() + 1;
        let mut par = vec![std::usize::MAX; size];
        let mut graph = vec![vec![]; size];

        for (from, to, weight) in edges {
            if from >= size || to >= size || from == to {
                return Err(InvalidTree);
            }
            if D::is_directed() {
                if par[to] != std::usize::MAX {
                    return Err(InvalidTree);
                }
                par[to] = from;
            }
            graph[from].push(Edge { to, weight });
            if !D::is_directed() {
                graph[to].push(Edge { to: from, weight });
            }
        }

        if !D::is_directed() {
            let mut nt = std::collections::VecDeque::new();
            nt.push_back(0);
            while let Some(now) = nt.pop_front() {
                for Edge { to, weight: _ } in &graph[now] {
                    if *to != par[now] {
                        if par[*to] != std::usize::MAX {
                            return Err(InvalidTree);
                        }
                        par[*to] = now;
                        nt.push_back(*to);
                    }
                }
            }
        }

        Ok(Tree {
            size,
            root: 0,
            par,
            graph,
            _d: std::marker::PhantomData,
        })
    }

    #[inline]
    pub fn from_edges(edges: Vec<(usize, usize)>) -> Result<Self, InvalidTree> {
        let edges = edges.into_iter().map(|(from, to)| (from, to, 1)).collect();
        Self::from_weighted_edges(edges)
    }

    /// The parent of root node is std::usize::MAX.
    #[inline]
    pub fn from_par_list(pars: Vec<usize>) -> Result<Self, InvalidTree> {
        let edges = pars
            .into_iter()
            .enumerate()
            .filter(|v| v.1 != std::usize::MAX)
            .map(|(i, par)| (par, i, 1))
            .collect();
        Self::from_weighted_edges(edges)
    }

    #[inline]
    pub fn neighbors(&'a self, index: usize) -> Neighbors<'a> {
        Neighbors {
            inner: self.graph[index].iter(),
        }
    }

    #[inline]
    pub fn edges(&'a self, index: usize) -> Edges<'a> {
        Edges {
            inner: self.graph[index].iter(),
        }
    }

    #[inline]
    pub fn edges_mut(&'a mut self, index: usize) -> EdgesMut<'a> {
        EdgesMut {
            inner: self.graph[index].iter_mut(),
        }
    }

    #[inline]
    pub fn root(&self) -> usize {
        self.root
    }

    #[inline]
    pub fn reroot(&mut self, new: usize) {
        self.root = new;
    }

    #[inline]
    pub fn reroot_with_rebuild(&mut self, new: usize) {
        self.reroot(new);
        self.rebuild();
    }

    fn rebuild(&mut self) {
        let mut nt = std::collections::VecDeque::new();
        nt.push_back((self.root, std::usize::MAX));

        while let Some((now, par)) = nt.pop_front() {
            for Edge { to, weight: _ } in &self.graph[now] {
                if par != *to {
                    self.par[*to] = now;
                    nt.push_back((*to, now));
                }
            }
        }
    }

    pub fn reroot_with_diameter(&mut self) {
        let mut dist = vec![-1; self.size];
        let mut nt = std::collections::BinaryHeap::new();
        nt.push(std::cmp::Reverse((0, self.root)));

        let mut max = (std::i64::MIN, 0);
        while let Some(std::cmp::Reverse((nd, now))) = nt.pop() {
            if dist[now] >= 0 {
                continue;
            }
            dist[now] = nd;
            max = std::cmp::max(max, (nd, now));

            for Edge { to, weight } in &self.graph[now] {
                if dist[*to] < 0 {
                    nt.push(std::cmp::Reverse((nd + weight, *to)));
                }
            }
        }

        self.reroot_with_rebuild(max.1);
    }
}

impl<D: Direction> std::convert::TryFrom<Vec<(usize, usize)>> for Tree<D> {
    type Error = InvalidTree;
    fn try_from(value: Vec<(usize, usize)>) -> Result<Self, Self::Error> {
        Self::from_edges(value)
    }
}

impl<D: Direction> std::convert::TryFrom<Vec<(usize, usize, i64)>> for Tree<D> {
    type Error = InvalidTree;
    fn try_from(value: Vec<(usize, usize, i64)>) -> Result<Self, Self::Error> {
        Self::from_weighted_edges(value)
    }
}

impl<D: Direction> std::convert::TryFrom<Vec<Vec<usize>>> for Tree<D> {
    type Error = InvalidTree;
    fn try_from(value: Vec<Vec<usize>>) -> Result<Self, Self::Error> {
        let edges = if D::is_directed() {
            value
                .into_iter()
                .enumerate()
                .map(|(from, v)| v.into_iter().map(move |to| (from, to)))
                .flatten()
                .collect()
        } else {
            value
                .into_iter()
                .enumerate()
                .map(|(from, v)| {
                    v.into_iter()
                        .filter(move |to| from <= *to)
                        .map(move |to| (from, to))
                })
                .flatten()
                .collect()
        };
        Self::from_edges(edges)
    }
}

impl<D: Direction> std::convert::TryFrom<Vec<Vec<(usize, i64)>>> for Tree<D> {
    type Error = InvalidTree;
    fn try_from(value: Vec<Vec<(usize, i64)>>) -> Result<Self, Self::Error> {
        let edges = if D::is_directed() {
            value
                .into_iter()
                .enumerate()
                .map(|(from, v)| v.into_iter().map(move |(to, weight)| (from, to, weight)))
                .flatten()
                .collect()
        } else {
            value
                .into_iter()
                .enumerate()
                .map(|(from, v)| {
                    v.into_iter()
                        .filter(move |(to, _)| from <= *to)
                        .map(move |(to, weight)| (from, to, weight))
                })
                .flatten()
                .collect()
        };
        Self::from_weighted_edges(edges)
    }
}

impl<D: Direction> std::convert::From<Tree<D>> for Graph<D> {
    fn from(from: Tree<D>) -> Self {
        Graph {
            size: from.size,
            graph: from.graph,
            _d: from._d,
        }
    }
}

/// If an ancestor earlier than its own rank is searched, std::usize::MAX is returned.  
pub fn nth_ancestor<D: Direction>(tree: &mut Tree<D>) -> impl Fn(usize, usize) -> usize {
    const MAX_RANK_LOG: usize = 25;
    let mut doubling = vec![vec![std::usize::MAX; tree.size]; MAX_RANK_LOG];

    if tree.par[tree.root] != std::usize::MAX {
        tree.rebuild();
    }

    for log in 0..MAX_RANK_LOG {
        for now in 0..tree.size {
            if log == 0 {
                doubling[log][now] = tree.par[now];
            } else {
                let to = doubling[log - 1][now];
                if to != std::usize::MAX {
                    doubling[log][now] = doubling[log - 1][to];
                }
            }
        }
    }

    move |mut now: usize, mut nth: usize| -> usize {
        for log in (0..MAX_RANK_LOG).rev() {
            if nth >= 1 << log {
                now = doubling[log][now];
                nth -= 1 << log;
                if now == std::usize::MAX {
                    break;
                }
            }
        }

        now
    }
}

/// Returns a closure that finds the Lowest Common Ancestor of the two vertices belonging to the tree.
pub fn lca<D: Direction>(tree: &mut Tree<D>) -> impl Fn(usize, usize) -> usize {
    const MAX_RANK_LOG: usize = 25;
    let mut doubling = vec![vec![std::usize::MAX; tree.size]; MAX_RANK_LOG];
    let mut rank = vec![std::usize::MAX; tree.size];

    if tree.par[tree.root] != std::usize::MAX {
        tree.rebuild();
    }

    let mut nt = std::collections::VecDeque::new();
    nt.push_back((tree.root, 0));
    while let Some((now, r)) = nt.pop_front() {
        if rank[now] != std::usize::MAX {
            continue;
        }
        rank[now] = r;

        for to in tree.neighbors(now) {
            if *to != tree.par[now] {
                nt.push_back((*to, r + 1));
            }
        }
    }

    for log in 0..MAX_RANK_LOG {
        for now in 0..tree.size {
            if log == 0 {
                doubling[log][now] = tree.par[now];
            } else {
                let to = doubling[log - 1][now];
                if to != std::usize::MAX {
                    doubling[log][now] = doubling[log - 1][to];
                }
            }
        }
    }

    move |mut l: usize, mut r: usize| -> usize {
        if rank[l] > rank[r] {
            std::mem::swap(&mut l, &mut r);
        }
        if rank[r] > rank[l] {
            let mut diff = rank[r] - rank[l];
            for log in (0..MAX_RANK_LOG).rev() {
                if diff >= 1 << log {
                    r = doubling[log][r];
                    diff -= 1 << log;
                }
            }
        }
        if l == r {
            return l;
        }

        for log in (0..MAX_RANK_LOG).rev() {
            if doubling[log][l] != doubling[log][r] {
                l = doubling[log][l];
                r = doubling[log][r];
            }
        }

        doubling[0][l]
    }
}

/// If the tree does not result in a normal tree (e.g., missing edges), return InvalidTree Error  
pub fn spanning_tree(graph: &Graph<UnDirected>) -> Result<Tree<UnDirected>, InvalidTree> {
    use unionfind::UnionFind;

    let mut nt = std::collections::BinaryHeap::new();
    for from in 0..graph.size {
        for (to, weight) in graph.edges(from) {
            nt.push(std::cmp::Reverse((*weight, from, *to)));
        }
    }

    let mut uf = UnionFind::new(graph.size);
    let mut edges = vec![];
    while let Some(std::cmp::Reverse((w, f, t))) = nt.pop() {
        if !uf.is_same(f, t) {
            edges.push((f, t, w));
            uf.merge(f, t);
        }
    }

    Tree::<UnDirected>::from_weighted_edges(edges)
}

#[cfg(test)]
mod tests {
    use super::{
        bellman_ford, dijkstra_heap, dijkstra_v2, low_link, scc, topological_sort, warshall_floyd,
        DirectedGraph, UnDirectedGraph,
    };

    #[test]
    fn graph_test() {
        // 9     1 --> 8 --> 4 --> 6     (0, 1, 3)           , (1, 8, 5)
        // ^     ^     |     |           (2, 0, 1), (2, 5, 9), (3, 0, 7), (3, 9, 3)
        // |     |     v     v           (4, 5, 4), (4, 6, 2),
        // 3 --> 0 <-- 2 --> 5           (7, 0, 8)           , (8, 2, 6), (8, 4, 1)
        //       ^
        //       |
        //       7
        let weighted_edges = vec![
            (0, 1, 3),
            (1, 8, 5),
            (2, 0, 1),
            (2, 5, 9),
            (3, 0, 7),
            (3, 9, 3),
            (4, 6, 2),
            (4, 5, 4),
            (7, 0, 8),
            (8, 2, 6),
            (8, 4, 1),
        ];
        let dir: DirectedGraph = DirectedGraph::from_weighted_edges(10, weighted_edges);

        let dist = dijkstra_heap(0, &dir);
        assert_eq!(
            dist,
            vec![
                0,
                3,
                14,
                std::i64::MAX,
                9,
                13,
                11,
                std::i64::MAX,
                8,
                std::i64::MAX
            ]
        );

        let dist = dijkstra_v2(0, &dir);
        assert_eq!(
            dist,
            vec![
                0,
                3,
                14,
                std::i64::MAX,
                9,
                13,
                11,
                std::i64::MAX,
                8,
                std::i64::MAX
            ]
        );

        let dists = warshall_floyd(&dir);
        assert_eq!(
            dists,
            vec![
                vec![
                    0,
                    3,
                    14,
                    std::i64::MAX,
                    9,
                    13,
                    11,
                    std::i64::MAX,
                    8,
                    std::i64::MAX
                ],
                vec![
                    12,
                    0,
                    11,
                    std::i64::MAX,
                    6,
                    10,
                    8,
                    std::i64::MAX,
                    5,
                    std::i64::MAX
                ],
                vec![
                    1,
                    4,
                    0,
                    std::i64::MAX,
                    10,
                    9,
                    12,
                    std::i64::MAX,
                    9,
                    std::i64::MAX
                ],
                vec![7, 10, 21, 0, 16, 20, 18, std::i64::MAX, 15, 3],
                vec![
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    0,
                    4,
                    2,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX
                ],
                vec![
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    0,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX
                ],
                vec![
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    0,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX
                ],
                vec![8, 11, 22, std::i64::MAX, 17, 21, 19, 0, 16, std::i64::MAX],
                vec![
                    7,
                    10,
                    6,
                    std::i64::MAX,
                    1,
                    5,
                    3,
                    std::i64::MAX,
                    0,
                    std::i64::MAX
                ],
                vec![
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    std::i64::MAX,
                    0
                ]
            ]
        );

        let groups = scc(&dir);
        let groups = groups
            .into_iter()
            .enumerate()
            .fold(vec![0; 10], |mut v, (i, g)| {
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
        let signed_weighted_edges = vec![
            (0, 1, 1),
            (1, 2, 2),
            (2, 3, -3),
            (2, 5, -6),
            (3, 4, 4),
            (4, 1, 1),
            (5, 6, 3),
            (6, 7, 7),
            (7, 8, -9),
            (8, 5, 4),
        ];
        let dir: DirectedGraph = DirectedGraph::from_weighted_edges(9, signed_weighted_edges);

        let dist = bellman_ford(0, &dir).unwrap();
        assert_eq!(dist, vec![0, 1, 3, 0, 4, -3, 0, 7, -2]);

        // 0 --> 1 --> 2 --> 5 --> 8    (0, 1), (1, 2), (1, 4), (2, 3), (2, 5),
        //       |     |     |     ^    (4, 3), (5, 6), (5, 8), (6, 7), (7, 8)
        //       v     v     v     |
        //       4 --> 3     6 --> 7
        let edges = vec![
            (0, 1),
            (1, 2),
            (1, 4),
            (2, 3),
            (2, 5),
            (4, 3),
            (5, 6),
            (5, 8),
            (6, 7),
            (7, 8),
        ];
        let dir: DirectedGraph = DirectedGraph::from_edges(9, edges);
        let list = topological_sort(&dir)
            .unwrap()
            .into_iter()
            .enumerate()
            .fold(vec![0; 9], |mut v, (i, s)| {
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
        let edges = vec![
            (0, 1),
            (1, 2),
            (1, 4),
            (2, 3),
            (2, 5),
            (3, 4),
            (5, 6),
            (5, 8),
            (6, 7),
            (7, 8),
        ];
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
        let mut undir =
            UnDirectedTree::from_par_list(vec![std::usize::MAX, 0, 0, 1, 1, 2, 3, 4, 4, 5, 7, 9])
                .unwrap();

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
        let set = (0..tree.size)
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
        assert_eq!(
            set,
            vec![
                (0, 1),
                (0, 2),
                (0, 7),
                (1, 8),
                (1, 9),
                (3, 9),
                (4, 5),
                (4, 6),
                (4, 8)
            ]
        );
    }

    #[test]
    #[should_panic]
    fn bellmanford_negative_cycle_detection() {
        // 0 --> 1 --> 2 --> 5 <-- 8    (0, 1, 1),              (1, 2, -5)
        //       ^     |     |     ^    (2, 3, -3), (2, 5, -6), (3, 4, 4)
        //       |     v     v     |    (4, 1, 1),              (5, 6, 3)
        //       4 <-- 3     6 --> 7    (6, 7, 7),              (7, 8, -9)
        //                              (8, 5, 4)
        let signed_weighted_edges = vec![
            (0, 1, 1),
            (1, 2, -5),
            (2, 3, -3),
            (2, 5, -6),
            (3, 4, 4),
            (4, 1, 1),
            (5, 6, 3),
            (6, 7, 7),
            (7, 8, -9),
            (8, 5, 4),
        ];
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
        let signed_weighted_edges = vec![
            (0, 1, 1),
            (1, 2, -5),
            (2, 3, -3),
            (2, 5, -6),
            (3, 4, 4),
            (4, 1, 1),
            (5, 6, 3),
            (6, 7, 7),
            (7, 8, -9),
            (8, 5, 4),
        ];
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
        let edges = vec![
            (1, 2, 3),
            (1, 3, 1),
            (1, 5, 7),
            (1, 8, 8),
            (3, 4, 9),
            (4, 6, 3),
            (5, 10, 4),
            (6, 7, 4),
            (6, 9, 1),
        ];

        // Panic!!!
        let _ = UnDirectedTree::from_weighted_edges(edges).unwrap();
    }
}
