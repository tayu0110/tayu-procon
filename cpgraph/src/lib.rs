mod bellman_ford;
mod cycle_detect;
mod dijkstra;
mod eulerian_trail;
mod low_link;
mod mst;
mod scc;
mod shortest_path;
mod topological_sort;
mod tree;
mod warshall_floyd;

use std::{fmt::Debug, ops::Range};

pub use bellman_ford::*;
pub use mst::*;
pub use tree::*;

#[derive(Debug, Clone)]
pub struct Edge<W: Clone> {
    to: u32,
    index: u32,
    weight: W,
}

impl<W: Clone> Edge<W> {
    pub fn to(&self) -> usize {
        self.to as usize
    }

    pub fn index(&self) -> usize {
        self.index as usize
    }

    pub fn weight(&self) -> &W {
        &self.weight
    }
}

pub struct EdgeFull<'a, W: Clone> {
    from: usize,
    edge: &'a Edge<W>,
}

impl<W: Clone> EdgeFull<'_, W> {
    pub fn from(&self) -> usize {
        self.from
    }

    pub fn to(&self) -> usize {
        self.edge.to()
    }

    pub fn index(&self) -> usize {
        self.edge.index()
    }

    pub fn weight(&self) -> &W {
        self.edge.weight()
    }
}

#[derive(Debug, Clone)]
pub struct FixedGraph<W: Clone, const DIR: bool> {
    vertexes: Vec<Range<usize>>,
    edges: Vec<Edge<W>>,
}

impl<W: Clone, const DIR: bool> FixedGraph<W, DIR> {
    pub fn from_edges(edges: impl IntoIterator<Item = (usize, usize, W)>) -> Self {
        let edges = edges
            .into_iter()
            .enumerate()
            .map(|(i, (from, to, weight))| (i as u32, from as u32, to as u32, weight))
            .collect::<Vec<_>>();
        if edges.is_empty() {
            return Self { vertexes: vec![], edges: vec![] };
        }

        Self::from_edges_with_index(edges)
    }

    /// Since `from_edges` automatically adds the index, use this if you want to construct a graph keeping the index value.
    ///
    /// `Item = (index, from, to, weight)`.  
    /// The doubling of edges in the case of `DIR == false` is done in the method.
    fn from_edges_with_index(iter: impl IntoIterator<Item = (u32, u32, u32, W)>) -> Self {
        let mut edges = iter.into_iter().collect::<Vec<_>>();

        if !DIR {
            edges = edges
                .iter()
                .map(|v| (v.0, v.2, v.1, v.3.clone()))
                .chain(edges.iter().cloned())
                .collect();
        }

        edges.sort_unstable_by_key(|v| v.1);
        let max = edges
            .iter()
            .flat_map(|v| [v.1, v.2])
            .max()
            .unwrap()
            .checked_add(1)
            .expect("The number of vertexes is too large") as usize;

        let mut vertexes = vec![0..0; max];
        let mut v = edges[0].1;
        let mut prev = 0;
        for (i, e) in edges.windows(2).enumerate() {
            if e[0].1 != e[1].1 {
                vertexes[v as usize] = prev..i + 1;
                prev = i + 1;
                v = e[1].1;
            }
        }
        vertexes[v as usize] = prev..edges.len();

        Self {
            vertexes,
            edges: edges
                .into_iter()
                .map(|(index, _, to, weight)| Edge { to, index, weight })
                .collect(),
        }
    }

    pub fn edges(
        &self,
        vertex: usize,
    ) -> impl Iterator<Item = &'_ Edge<W>> + ExactSizeIterator + '_ {
        let range = self.vertexes[vertex].clone();
        self.edges[range].iter()
    }

    pub fn edges_all(&self) -> impl Iterator<Item = EdgeFull<'_, W>> + '_ {
        (0..self.num_vertexes())
            .flat_map(|i| self.edges(i).map(move |edge| EdgeFull { from: i, edge }))
    }

    pub fn num_edges(&self) -> usize {
        self.edges.len() >> (1 - DIR as u8)
    }

    pub fn num_vertexes(&self) -> usize {
        self.vertexes.len()
    }

    pub fn nth_edge(&self, vertex: usize, nth: usize) -> Option<&Edge<W>> {
        let range = self.vertexes[vertex].clone();
        let index = range.start.saturating_add(nth);
        range.contains(&index).then(|| &self.edges[index])
    }
}

impl<W, I, const DIR: bool> From<(usize, I)> for FixedGraph<W, DIR>
where
    W: Clone,
    I: IntoIterator,
    Self: FromIterator<I::Item>,
{
    fn from(value: (usize, I)) -> Self {
        let (n, iter) = value;
        let mut graph = iter.into_iter().collect::<Self>();
        assert!(n >= graph.num_vertexes());
        graph.vertexes.resize_with(n, || 0..0);
        graph
    }
}

impl<W: Clone, const DIR: bool> FromIterator<(usize, usize, W)> for FixedGraph<W, DIR> {
    fn from_iter<T: IntoIterator<Item = (usize, usize, W)>>(iter: T) -> Self {
        Self::from_edges(iter)
    }
}

impl<const DIR: bool> FromIterator<(usize, usize)> for FixedGraph<(), DIR> {
    fn from_iter<T: IntoIterator<Item = (usize, usize)>>(iter: T) -> Self {
        Self::from_edges(iter.into_iter().map(|(f, t)| (f, t, ())))
    }
}

pub trait SaturatingOps: Clone {
    const MAX: Self;
    const MIN: Self;
    fn saturating_add(&self, rhs: &Self) -> Self;
}

macro_rules! impl_saturating_ops {
    ( $( $t:ty ),* ) => {
        $(
            impl SaturatingOps for $t {
                const MAX: $t = <$t>::MAX;
                const MIN: $t = <$t>::MIN;
                fn saturating_add(&self, rhs: &$t) -> $t {
                    <$t>::saturating_add(*self, *rhs)
                }
            }
        )*
    };
}

impl_saturating_ops!(i8, i16, i32, i64, isize, i128, u8, u16, u32, u64, usize, u128);
