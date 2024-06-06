use crate::{FixedGraph, SaturatingOps};

impl<W: SaturatingOps + Default + Ord, const DIR: bool> FixedGraph<W, DIR> {
    /// Find the single starting point shortest path by Bellman-Ford's algorithm.  
    /// The information of the paths can be accessed from returned `BellmanFord`.
    pub fn bellman_ford(&self, src: usize) -> BellmanFord<W> {
        let mut dist = vec![W::MAX; self.num_vertexes()];
        dist[src] = W::default();
        let mut prev = vec![usize::MAX; self.num_vertexes()];
        prev[src] = src;

        for i in 0..self.num_vertexes() * 2 {
            let mut updated = false;
            for from in 0..self.num_vertexes() {
                if prev[from] < usize::MAX {
                    for e in self.edges(from) {
                        let new = dist[from].saturating_add(e.weight());
                        if dist[e.to()] > new {
                            if i < self.num_vertexes() - 1 {
                                dist[e.to()] = new;
                            } else {
                                dist[e.to()] = W::MIN;
                            }
                            prev[e.to()] = from;
                            updated = true;
                        }
                    }
                }
            }
            if !updated {
                break;
            }
        }

        BellmanFord { src, prev, dist }
    }
}

pub struct BellmanFord<W: SaturatingOps + Ord> {
    src: usize,
    prev: Vec<usize>,
    dist: Vec<W>,
}

impl<W: SaturatingOps + Ord> BellmanFord<W> {
    /// If there is a shortest path that does not contain a negative cycle, return the weights and its shortest path.  
    /// If not (contains some negative cycles, or has no paths), return `None`.
    pub fn shortest_path(&self, to: usize) -> Option<(W, Vec<usize>)> {
        (W::MIN < self.dist[to] && self.dist[to] < W::MAX && W::MIN < self.dist[self.src]).then(
            || {
                let w = self.dist[to].clone();
                let mut path = vec![];
                let mut now = to;
                while self.prev[now] != now {
                    path.push(now);
                    now = self.prev[now];
                }
                path.push(now);
                path.reverse();
                (w, path)
            },
        )
    }

    /// If there is a path to `to`, return the cost.  
    /// If the return value is `W::MIN`, the cost is negative infinity because it is contained in a negative cycle.  
    /// If the return value is `None`, there are no paths to `to`.
    pub fn cost(&self, to: usize) -> Option<W> {
        self.has_path(to).then(|| self.dist[to].clone())
    }

    /// Check if there are any paths between `src` and `to`.
    pub fn has_path(&self, to: usize) -> bool {
        self.dist[to] < W::MAX
    }

    /// Check the vertex `index` is placed in a negative cycle.
    pub fn in_negative_cycle(&self, index: usize) -> bool {
        self.dist[index] == W::MIN
    }
}
