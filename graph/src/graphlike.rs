use crate::{Direction, Edges, EdgesMut, Graph, Neighbors, Tree};

pub trait GraphLike {
    fn size(&self) -> usize;
    fn neighbors(&'_ self, index: usize) -> Neighbors<'_>;
    fn edges(&'_ self, index: usize) -> Edges<'_>;
}

impl<D: Direction> GraphLike for Graph<D> {
    fn size(&self) -> usize {
        self.size()
    }
    fn neighbors(&'_ self, index: usize) -> Neighbors<'_> {
        self.neighbors(index)
    }
    fn edges(&'_ self, index: usize) -> Edges<'_> {
        self.edges(index)
    }
}

impl<D: Direction> GraphLike for Tree<D> {
    fn size(&self) -> usize {
        self.size()
    }
    fn neighbors(&'_ self, index: usize) -> Neighbors<'_> {
        self.neighbors(index)
    }
    fn edges(&'_ self, index: usize) -> Edges<'_> {
        self.edges(index)
    }
}

impl GraphLike for Vec<Vec<usize>> {
    fn size(&self) -> usize {
        self.len()
    }
    fn neighbors(&'_ self, index: usize) -> Neighbors<'_> {
        Neighbors { inner: Box::new(self[index].iter()) }
    }
    fn edges(&'_ self, index: usize) -> Edges<'_> {
        Edges { inner: Box::new(self[index].iter().map(|to| (to, &1))) }
    }
}

impl GraphLike for Vec<Vec<(usize, i64)>> {
    fn size(&self) -> usize {
        self.len()
    }
    fn neighbors(&'_ self, index: usize) -> Neighbors<'_> {
        Neighbors { inner: Box::new(self[index].iter().map(|(to, _)| to)) }
    }
    fn edges(&'_ self, index: usize) -> Edges<'_> {
        Edges {
            inner: Box::new(self[index].iter().map(|(to, weight)| (to, weight))),
        }
    }
}

pub trait WeightedGraphLike {
    fn edges_mut(&'_ mut self, index: usize) -> EdgesMut<'_>;
}

impl<D: Direction> WeightedGraphLike for Graph<D> {
    fn edges_mut(&'_ mut self, index: usize) -> EdgesMut<'_> {
        self.edges_mut(index)
    }
}

impl WeightedGraphLike for Vec<Vec<(usize, i64)>> {
    fn edges_mut(&'_ mut self, index: usize) -> EdgesMut<'_> {
        EdgesMut {
            inner: Box::new(self[index].iter_mut().map(|(to, weight)| (&*to, weight))),
        }
    }
}
