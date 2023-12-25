use graph::minimum_spanning_tree_from_edge;
use iolib::*;
use std::collections::HashSet;

fn main() {
    scan!(n: usize, m: usize, e: [(usize, usize, i64); m]);

    let edge = minimum_spanning_tree_from_edge(n, e.clone()).collect::<HashSet<_>>();

    let res = e
        .into_iter()
        .enumerate()
        .filter_map(|(i, (s, d, w))| {
            (edge.contains(&(s, d, w)) || edge.contains(&(d, s, w))).then_some((i, w))
        })
        .unzip::<usize, i64, Vec<usize>, Vec<i64>>();
    putln!(res.1.into_iter().sum::<i64>());
    putitln!(res.0.into_iter(), sep = ' ');
}
