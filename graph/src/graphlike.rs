use crate::{Direction, Edges, EdgesMut, Graph, Neighbors, Tree};

pub trait GraphLike {
    fn size(&self) -> usize;
    fn neighbors(&self, index: usize) -> Neighbors;
    fn edges(&self, index: usize) -> Edges;
}

impl<D: Direction> GraphLike for Graph<D> {
    fn size(&self) -> usize { self.size() }
    fn neighbors(&self, index: usize) -> Neighbors { self.neighbors(index) }
    fn edges(&self, index: usize) -> Edges { self.edges(index) }
}

impl<D: Direction> GraphLike for Tree<D> {
    fn size(&self) -> usize { self.size() }
    fn neighbors(&self, index: usize) -> Neighbors { self.neighbors(index) }
    fn edges(&self, index: usize) -> Edges { self.edges(index) }
}

impl GraphLike for Vec<Vec<usize>> {
    fn size(&self) -> usize { self.len() }
    fn neighbors(&self, index: usize) -> Neighbors { Neighbors { inner: Box::new(self[index].iter()) } }
    fn edges(&self, index: usize) -> Edges { Edges { inner: Box::new(self[index].iter().map(|to| (to, &1))) } }
}

impl GraphLike for Vec<Vec<(usize, i64)>> {
    fn size(&self) -> usize { self.len() }
    fn neighbors(&self, index: usize) -> Neighbors { Neighbors { inner: Box::new(self[index].iter().map(|(to, _)| to)) } }
    fn edges(&self, index: usize) -> Edges {
        Edges {
            inner: Box::new(self[index].iter().map(|(to, weight)| (to, weight))),
        }
    }
}

pub trait WeightedGraphLike {
    fn edges_mut(&mut self, index: usize) -> EdgesMut;
}

impl<D: Direction> WeightedGraphLike for Graph<D> {
    fn edges_mut(&mut self, index: usize) -> EdgesMut { self.edges_mut(index) }
}

impl WeightedGraphLike for Vec<Vec<(usize, i64)>> {
    fn edges_mut(&mut self, index: usize) -> EdgesMut {
        EdgesMut {
            inner: Box::new(self[index].iter_mut().map(|(to, weight)| (&*to, weight))),
        }
    }
}
