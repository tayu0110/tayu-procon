use super::{Directed, Direction, Edge, Edges, EdgesMut, Neighbors, UnDirected};

pub type DirectedGraph = Graph<Directed>;
pub type UnDirectedGraph = Graph<UnDirected>;

#[derive(Debug, Clone)]
pub struct Graph<D: Direction> {
    pub size: usize,
    pub graph: Vec<Vec<Edge>>,
    pub _d: std::marker::PhantomData<D>,
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
    pub fn size(&self) -> usize { self.size }

    #[inline]
    pub fn from_weighted_edges(size: usize, edges: Vec<(usize, usize, i64)>) -> Self {
        edges.into_iter().fold(Self::new(size), |mut g, (from, to, weight)| {
            g.set_weighted_edge(from, to, weight);
            g
        })
    }

    #[inline]
    pub fn from_edges(size: usize, edges: Vec<(usize, usize)>) -> Self {
        edges.into_iter().fold(Self::new(size), |mut g, (from, to)| {
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
    pub fn set_edge(&mut self, from: usize, to: usize) { self.set_weighted_edge(from, to, 1) }

    #[inline]
    pub fn resize(&mut self, size: usize) {
        self.size = size;
        self.graph.resize(size, vec![]);
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

    pub fn rev_graph(&self) -> Self {
        let mut graph = vec![vec![]; self.size];

        for from in 0..self.size {
            for Edge { to, weight } in &self.graph[from] {
                graph[*to].push(Edge { to: from, weight: *weight });
            }
        }

        Self { size: self.size, graph, _d: std::marker::PhantomData }
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
            from.into_iter().enumerate().map(|(from, v)| v.into_iter().map(move |to| (from, to))).flatten().collect()
        } else {
            from.into_iter()
                .enumerate()
                .map(|(from, v)| v.into_iter().filter(move |to| from <= *to).map(move |to| (from, to)))
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
                .map(|(from, v)| v.into_iter().filter(move |(to, _)| from <= *to).map(move |(to, weight)| (from, to, weight)))
                .flatten()
                .collect()
        };

        Graph::<D>::from_weighted_edges(size, edges)
    }
}
