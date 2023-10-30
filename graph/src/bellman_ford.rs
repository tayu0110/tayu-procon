use super::{GraphLike, NegativeCycleError};

/// Find the single starting point shortest path by Bellman-Ford's algorithm.  
/// If the graph has negative cycle, return NegativeCycleError and the solution updated with std::i64::MIN for the cost of the vertices affected by the negative cycle.  
pub fn bellman_ford(
    from: usize,
    graph: &impl GraphLike,
) -> Result<Vec<i64>, (NegativeCycleError, Vec<i64>)> {
    const INF: i64 = i64::MAX;
    let mut res = vec![INF; graph.size()];
    res[from] = 0;

    let mut negative_cycle = false;
    for i in 0..graph.size() * 2 {
        let mut updated = false;
        for from in 0..graph.size() {
            for (to, weight) in graph.edges(from) {
                if res[*to] > res[from] + *weight {
                    if i < graph.size() - 1 {
                        res[*to] = res[from] + *weight;
                    } else {
                        res[*to] = i64::MIN;
                        negative_cycle = true;
                    }
                    updated = true;
                }
            }
        }
        if !updated {
            break;
        }
    }

    if negative_cycle {
        Err((NegativeCycleError, res))
    } else {
        Ok(res)
    }
}
