use crate::{FixedGraph, SaturatingOps};

impl<W, const DIR: bool> FixedGraph<W, DIR>
where
    W: Clone + SaturatingOps + Default + Ord,
{
    pub fn warshall_floyd(&self) -> Vec<Vec<W>> {
        let mut res = vec![vec![W::MAX; self.num_vertexes()]; self.num_vertexes()];

        for (from, res) in res.iter_mut().enumerate() {
            res[from] = W::default();
            for e in self.edges(from) {
                res[e.to()] = e.weight().clone();
            }
        }

        for k in 0..self.num_vertexes() {
            for i in 0..self.num_vertexes() {
                for j in 0..self.num_vertexes() {
                    res[i][j] = res[i][j].clone().min(res[i][k].saturating_add(&res[k][j]));
                }
            }
        }

        res
    }
}
