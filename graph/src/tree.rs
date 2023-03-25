use std::{collections::VecDeque, marker::PhantomData};

use super::{Directed, Direction, Edge, Edges, EdgesMut, Graph, InvalidTree, Neighbors, UnDirected};

pub type DirectedTree = Tree<Directed>;
pub type UnDirectedTree = Tree<UnDirected>;

#[derive(Debug, Clone)]
pub struct Tree<D: Direction> {
    size: usize,
    root: usize,
    par: Option<Vec<usize>>,
    pub graph: Vec<Vec<Edge>>,
    _d: std::marker::PhantomData<D>,
}

impl<'a, D: Direction> Tree<D> {
    #[inline]
    pub fn size(&self) -> usize { self.size }

    fn make_parlist(&mut self) {
        let mut par = vec![std::usize::MAX; self.size];

        let mut nt = VecDeque::new();
        nt.push_back(self.root);
        while let Some(now) = nt.pop_front() {
            for &to in self.neighbors(now) {
                if par[now] != to && par[to] == std::usize::MAX {
                    par[to] = now;
                    nt.push_back(to);
                }
            }
        }

        self.par = Some(par);
    }

    pub fn parent(&mut self, v: usize) -> usize {
        if self.par.is_none() {
            self.make_parlist();
        }
        self.par.as_ref().unwrap()[v]
    }

    pub fn from_weighted_edges(edges: Vec<(usize, usize, i64)>) -> Result<Self, InvalidTree> {
        let size = edges.len() + 1;
        let mut graph = vec![vec![]; size];
        let mut par = vec![false; size];

        for (from, to, weight) in edges {
            if from >= size || to >= size || from == to {
                return Err(InvalidTree);
            }
            if D::is_directed() && par[to] {
                return Err(InvalidTree);
            }
            par[to] = true;
            graph[from].push(Edge { to, weight });
            if !D::is_directed() {
                graph[to].push(Edge { to: from, weight });
            }
        }

        Ok(Tree { size, root: 0, par: None, graph, _d: PhantomData })
    }

    #[inline]
    pub fn from_edges(edges: Vec<(usize, usize)>) -> Result<Self, InvalidTree> {
        let edges = edges.into_iter().map(|(from, to)| (from, to, 1)).collect();
        Self::from_weighted_edges(edges)
    }

    /// The parent of root node is std::usize::MAX.
    #[inline]
    pub fn from_par_list(pars: Vec<usize>) -> Result<Self, InvalidTree> {
        let edges = pars.into_iter().enumerate().filter(|v| v.1 != std::usize::MAX).map(|(i, par)| (par, i, 1)).collect();
        Self::from_weighted_edges(edges)
    }

    #[inline]
    pub fn neighbors(&'a self, index: usize) -> Neighbors<'a> {
        Neighbors {
            inner: Box::new(self.graph[index].iter().map(|Edge { to, weight: _ }| to)),
        }
    }

    #[inline]
    pub fn edges(&'a self, index: usize) -> Edges<'a> {
        Edges {
            inner: Box::new(self.graph[index].iter().map(|Edge { to, weight }| (to, weight))),
        }
    }

    #[inline]
    pub fn edges_mut(&'a mut self, index: usize) -> EdgesMut<'a> {
        EdgesMut {
            inner: Box::new(self.graph[index].iter_mut().map(|Edge { to, weight }| (&*to, weight))),
        }
    }

    #[inline]
    pub fn root(&self) -> usize { self.root }

    #[inline]
    pub fn reroot(&mut self, new: usize) { self.root = new; }

    #[inline]
    pub fn reroot_with_rebuild(&mut self, new: usize) {
        self.reroot(new);
        self.rebuild();
    }

    pub fn rebuild(&mut self) {
        let mut nt = std::collections::VecDeque::new();
        nt.push_back((self.root, std::usize::MAX));
        self.par = None;
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
    fn try_from(value: Vec<(usize, usize)>) -> Result<Self, Self::Error> { Self::from_edges(value) }
}

impl<D: Direction> std::convert::TryFrom<Vec<(usize, usize, i64)>> for Tree<D> {
    type Error = InvalidTree;
    fn try_from(value: Vec<(usize, usize, i64)>) -> Result<Self, Self::Error> { Self::from_weighted_edges(value) }
}

impl<D: Direction> std::convert::From<Vec<Vec<usize>>> for Tree<D> {
    fn from(g: Vec<Vec<usize>>) -> Self {
        let mut graph = vec![vec![]; g.len()];
        for i in 0..g.len() {
            for &to in &g[i] {
                graph[i].push(Edge { to, weight: 1 });
            }
        }
        Self {
            root: 0,
            size: graph.len(),
            par: None,
            graph,
            _d: PhantomData,
        }
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
                .map(|(from, v)| v.into_iter().filter(move |(to, _)| from <= *to).map(move |(to, weight)| (from, to, weight)))
                .flatten()
                .collect()
        };
        Self::from_weighted_edges(edges)
    }
}

impl<D: Direction> std::convert::From<Tree<D>> for Graph<D> {
    fn from(from: Tree<D>) -> Self { Graph { size: from.size, graph: from.graph, _d: from._d } }
}
