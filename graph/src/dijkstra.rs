use super::{Direction, Graph, GraphLike};
use std::cmp::Reverse;
use std::collections::BinaryHeap;

/// Find the single starting point shortest path by Dijkstra's algorithm.  
/// The computational complexity is O(ElogV), where E is the number of edges and V is the number of vertices, because a BinaryHeap is used.  
/// If there is an unreachable vertex, the distance of that vertex is i64::MAX  
pub fn dijkstra_heap(from: usize, graph: &impl GraphLike) -> Vec<i64> {
    let mut res = vec![i64::MAX; graph.size()];

    let mut nt = BinaryHeap::new();
    nt.push(Reverse((0, from)));

    while let Some(Reverse((nd, now))) = nt.pop() {
        if res[now] != i64::MAX {
            continue;
        }
        res[now] = nd;

        for (to, weight) in graph.edges(now).filter(|&(&to, _)| res[to] == i64::MAX) {
            nt.push(Reverse((nd + *weight, *to)));
        }
    }

    res
}

/// Find the single starting point shortest path by Dijkstra's algorithm.  
/// The computational complexity is O(V^2), where V is the number of vertices.  
/// If there is an unreachable vertex, the distance of that vertex is i64::MAX  
pub fn dijkstra_v2<D: Direction>(from: usize, graph: &Graph<D>) -> Vec<i64> {
    let mut res = vec![i64::MAX; graph.size()];
    let mut checked = vec![false; graph.size()];
    res[from] = 0;

    let mut now = from;
    for _ in 0..graph.size() {
        checked[now] = true;
        for (to, weight) in graph.edges(now) {
            res[*to] = res[*to].min(res[now] + *weight);
        }
        if let Some((_, to)) = checked
            .iter()
            .enumerate()
            .filter_map(|(next, &checked)| if !checked && res[next] != i64::MAX { Some((res[next], next)) } else { None })
            .min()
        {
            now = to;
            continue;
        }
        break;
    }

    res
}
