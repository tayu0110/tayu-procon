use super::{Graph, InvalidTree, Tree, UnDirected};
use std::cmp::Reverse;
use std::collections::{BTreeMap, BinaryHeap};
use unionfind::UnionFind;

/// If the tree does not result in a normal tree (e.g., missing edges), return InvalidTree Error  
pub fn spanning_tree(graph: &Graph<UnDirected>) -> Result<Tree<UnDirected>, InvalidTree> {
    let mut nt = BinaryHeap::new();
    for from in 0..graph.size() {
        for (to, weight) in graph.edges(from) {
            nt.push(Reverse((*weight, from, *to)));
        }
    }

    let mut uf = UnionFind::new(graph.size());
    let mut edges = vec![];
    while let Some(Reverse((w, f, t))) = nt.pop() {
        if !uf.is_same(f, t) {
            edges.push((f, t, w));
            uf.merge(f, t);
        }
    }

    Tree::<UnDirected>::from_weighted_edges(edges)
}

// https://hitonanode.github.io/cplib-cpp/graph/manhattan_mst.hpp
/// xy :    [(x0, y0), (x1, y1), (x2, y2), ...]
/// return [(weight0, from0, to0), (weight1, from1, to1), (weight2, from2, to2), ...]
pub fn manhattan_minimum_spanning_tree(xy: &Vec<(i64, i64)>) -> Vec<(i64, usize, usize)> {
    let (mut xs, mut ys) = xy
        .into_iter()
        .cloned()
        .unzip::<i64, i64, Vec<i64>, Vec<i64>>();
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
                    res.push((
                        ((xs[i] - xs[j]) as i64).abs() + ((ys[i] - ys[j]) as i64).abs(),
                        i,
                        j,
                    ));
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
