use super::{Directed, Graph};

/// Perform strongly connected component decomposition of a directed graph by Kosaraju's algorithm.  
/// The decomposed strongly connected components are ordered topologically and returned as two-dimensional vectors.  
pub fn scc(graph: &Graph<Directed>) -> Vec<Vec<usize>> {
    let rev_graph = graph.rev_graph();

    let mut used = vec![false; graph.size()];
    let mut order = vec![];
    for start in 0..graph.size() {
        if !used[start] {
            dfs_for_scc(start, &mut used, &mut order, &graph);
        }
    }

    let mut group = 0;
    let mut groups = vec![-1; graph.size()];
    let mut res = vec![];
    while let Some(now) = order.pop() {
        if groups[now] < 0 {
            let mut list = vec![];
            rdfs_for_scc(now, group, &mut groups, &mut list, &rev_graph);
            group += 1;
            res.push(list);
        }
    }

    res
}

fn dfs_for_scc(now: usize, used: &mut Vec<bool>, order: &mut Vec<usize>, graph: &Graph<Directed>) {
    used[now] = true;
    for &to in graph.neighbors(now) {
        if !used[to] {
            dfs_for_scc(to, used, order, graph);
        }
    }
    order.push(now);
}

fn rdfs_for_scc(now: usize, group: i32, groups: &mut Vec<i32>, list: &mut Vec<usize>, graph: &Graph<Directed>) {
    groups[now] = group;
    for &to in graph.neighbors(now) {
        if groups[to] < 0 {
            rdfs_for_scc(to, group, groups, list, graph);
        }
    }
    list.push(now);
}
