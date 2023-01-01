use super::{Graph, InvalidTree, Tree, UnDirected};
use unionfind::UnionFind;

/// If the tree does not result in a normal tree (e.g., missing edges), return InvalidTree Error  
pub fn spanning_tree(graph: &Graph<UnDirected>) -> Result<Tree<UnDirected>, InvalidTree> {
    let mut nt = std::collections::BinaryHeap::new();
    for from in 0..graph.size() {
        for (to, weight) in graph.edges(from) {
            nt.push(std::cmp::Reverse((*weight, from, *to)));
        }
    }

    let mut uf = UnionFind::new(graph.size());
    let mut edges = vec![];
    while let Some(std::cmp::Reverse((w, f, t))) = nt.pop() {
        if !uf.is_same(f, t) {
            edges.push((f, t, w));
            uf.merge(f, t);
        }
    }

    Tree::<UnDirected>::from_weighted_edges(edges)
}
