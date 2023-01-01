use super::{Direction, Graph};

/// Find the single starting point shortest path by Dijkstra's algorithm.  
/// The computational complexity is O(ElogV), where E is the number of edges and V is the number of vertices, because a BinaryHeap is used.  
/// If there is an unreachable vertex, the distance of that vertex is std::i64::MAX  
pub fn dijkstra_heap<D: Direction>(from: usize, graph: &Graph<D>) -> Vec<i64> {
    let mut res = vec![std::i64::MAX; graph.size()];

    let mut nt = std::collections::BinaryHeap::new();
    nt.push(std::cmp::Reverse((0, from)));

    while let Some(std::cmp::Reverse((nd, now))) = nt.pop() {
        if res[now] != std::i64::MAX {
            continue;
        }
        res[now] = nd;

        for (to, weight) in graph.edges(now).filter(|&(&to, _)| res[to] == std::i64::MAX) {
            nt.push(std::cmp::Reverse((nd + *weight, *to)));
        }
    }

    res
}

/// Find the single starting point shortest path by Dijkstra's algorithm.  
/// The computational complexity is O(V^2), where V is the number of vertices.  
/// If there is an unreachable vertex, the distance of that vertex is std::i64::MAX  
pub fn dijkstra_v2<D: Direction>(from: usize, graph: &Graph<D>) -> Vec<i64> {
    let mut res = vec![std::i64::MAX; graph.size()];
    let mut checked = vec![false; graph.size()];
    res[from] = 0;

    let mut now = from;
    for _ in 0..graph.size() {
        checked[now] = true;
        for (to, weight) in graph.edges(now) {
            res[*to] = std::cmp::min(res[*to], res[now] + *weight);
        }
        if let Some((_, to)) = checked
            .iter()
            .enumerate()
            .filter_map(|(next, &checked)| if !checked && res[next] != std::i64::MAX { Some((res[next], next)) } else { None })
            .min()
        {
            now = to;
            continue;
        }
        break;
    }

    res
}
