use super::{Graph, InvalidTree, Tree, UnDirected};
use std::collections::BTreeMap;
use unionfind::UnionFind;

/// If the tree does not result in a normal tree (e.g., missing edges), return InvalidTree Error  
pub fn spanning_tree(graph: &Graph<UnDirected>) -> Result<Tree<UnDirected>, InvalidTree> {
    Tree::from_weighted_edges(
        minimum_spanning_tree_from_edge(
            graph.size(),
            (0..graph.size()).flat_map(|i| {
                graph
                    .edges(i)
                    .filter_map(move |(&to, &w)| (i < to).then_some((i, to, w)))
            }),
        )
        .collect::<Vec<_>>(),
    )
}

/// Receive `size` which is the size of this graph and `edges` which is the undirected edges of this graph represented (u, v, weight).
///
/// The elements of `edges` need not be unique. <br/>
/// In other words, the graph as this function's argument need not be simple graph.
pub fn minimum_spanning_tree_from_edge(
    size: usize,
    edges: impl IntoIterator<Item = (usize, usize, i64)>,
) -> impl Iterator<Item = (usize, usize, i64)> {
    let mut edges = edges
        .into_iter()
        .map(|(s, d, w)| (s.min(d), s.max(d), w))
        .collect::<Vec<_>>();
    edges.sort_unstable_by_key(|&(s, d, w)| (w, s, d));
    edges.dedup();

    let mut uf = UnionFind::new(size);
    edges.into_iter().filter(move |&(s, d, _)| uf.merge(s, d))
}

// https://hitonanode.github.io/cplib-cpp/graph/manhattan_mst.hpp
/// xy :    [(x0, y0), (x1, y1), (x2, y2), ...]
/// return [(weight0, from0, to0), (weight1, from1, to1), (weight2, from2, to2), ...]
pub fn manhattan_minimum_spanning_tree(xy: &[(i64, i64)]) -> Vec<(i64, usize, usize)> {
    let (mut xs, mut ys) = xy.iter().cloned().unzip::<i64, i64, Vec<i64>, Vec<i64>>();
    let n = xy.len();
    let mut idx = (0..n).collect::<Vec<_>>();
    let mut res: Vec<(i64, usize, usize)> = vec![];
    for _ in 0..2 {
        for _ in 0..2 {
            idx.sort_by(|&i, &j| (xs[i] + ys[i]).cmp(&(xs[j] + ys[j])));
            let mut sweep = BTreeMap::new();
            for &i in &idx {
                while let Some((&k, &j)) = sweep.range(-ys[i]..).next() {
                    if xs[i] - xs[j] < ys[i] - ys[j] {
                        break;
                    }
                    res.push((i64::abs(xs[i] - xs[j]) + i64::abs(ys[i] - ys[j]), i, j));
                    sweep.remove(&k);
                }
                sweep.insert(-ys[i], i);
            }
            std::mem::swap(&mut xs, &mut ys);
        }
        xs.iter_mut().for_each(|x| *x = -*x);
    }

    res.sort();
    res
}
