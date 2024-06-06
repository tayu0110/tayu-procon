use std::{cmp::Reverse, collections::BinaryHeap};

use crate::{FixedGraph, SaturatingOps};

fn heap<W, const DIR: bool>(src: usize, graph: &FixedGraph<W, DIR>) -> Dijkstra<W>
where
    W: Clone + Default + SaturatingOps + Ord,
{
    let mut dist = vec![W::MAX; graph.num_vertexes()];
    let mut prev = vec![usize::MAX; graph.num_vertexes()];

    let mut nt = BinaryHeap::from([Reverse((W::default(), src, src))]);
    while let Some(Reverse((w, now, p))) = nt.pop() {
        if prev[now] != usize::MAX {
            continue;
        }
        dist[now] = w.clone();
        prev[now] = p;

        for e in graph.edges(now) {
            if prev[e.to()] == usize::MAX {
                nt.push(Reverse((w.saturating_add(e.weight()), e.to(), now)));
            }
        }
    }

    Dijkstra { prev, dist }
}

fn v2<W, const DIR: bool>(src: usize, graph: &FixedGraph<W, DIR>) -> Dijkstra<W>
where
    W: Clone + Default + SaturatingOps + Ord,
{
    let mut dist = vec![W::MAX; graph.num_vertexes()];
    let mut prev = vec![usize::MAX; graph.num_vertexes()];
    let mut decided = vec![false; graph.num_vertexes()];
    dist[src] = W::default();
    prev[src] = src;
    decided[src] = true;

    let mut now = src;
    for _ in 0..graph.num_vertexes() - 1 {
        for e in graph.edges(now) {
            let new = dist[now].saturating_add(e.weight());
            if new < dist[e.to()] {
                dist[e.to()] = new;
                prev[e.to()] = now;
            }
        }

        let mut max = W::MAX;
        for i in (0..graph.num_vertexes()).filter(|&i| !decided[i]) {
            if max > dist[i] {
                max = dist[i].clone();
                now = i;
            }
        }

        decided[now] = true;
    }

    Dijkstra { prev, dist }
}

impl<W, const DIR: bool> FixedGraph<W, DIR>
where
    W: Clone + Default + SaturatingOps + Ord,
{
    /// Find paths and costs from `src` to reachable vertexes using Dijkstra algorithm.  
    /// The information of paths can be accessed from returned `Dijkstra`.
    ///
    /// # Constraint
    /// - For graphs with edges with negative weights, this method does not work correctly.
    pub fn dijkstra(&self, src: usize) -> Dijkstra<W> {
        let v = self.num_vertexes();
        let e = self.num_edges();

        if v * v < e * v.checked_next_power_of_two().unwrap_or(1).trailing_zeros() as usize {
            v2(src, self)
        } else {
            heap(src, self)
        }
    }
}

#[derive(Debug, Clone)]
pub struct Dijkstra<W> {
    prev: Vec<usize>,
    dist: Vec<W>,
}

impl<W: Clone + SaturatingOps + Ord> Dijkstra<W> {
    /// If there is a shortest path, return the weights and its shortest path.  
    /// If not, return `None`.
    pub fn shortest_path(&self, to: usize) -> Option<(W, Vec<usize>)> {
        (self.dist[to] < W::MAX).then(|| {
            let mut path = vec![];
            let mut now = to;
            while self.prev[now] != now {
                path.push(now);
                now = self.prev[now];
            }
            path.push(now);
            path.reverse();
            (self.dist[to].clone(), path)
        })
    }

    /// If there is a path to `to`, return the cost.  
    /// If the return value is `None`, there are no paths to `to`.
    pub fn cost(&self, to: usize) -> Option<W> {
        self.has_path(to).then(|| self.dist[to].clone())
    }

    /// Check if there are any paths between `src` and `to`.
    pub fn has_path(&self, to: usize) -> bool {
        self.dist[to] < W::MAX
    }
}
