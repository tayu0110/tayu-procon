use super::GraphLike;

pub fn warshall_floyd(graph: &impl GraphLike) -> Vec<Vec<i64>> {
    let mut res = vec![vec![i64::MAX; graph.size()]; graph.size()];

    for from in 0..graph.size() {
        res[from][from] = 0;
        for (to, weight) in graph.edges(from) {
            res[from][*to] = *weight;
        }
    }

    for k in 0..graph.size() {
        for i in 0..graph.size() {
            for j in 0..graph.size() {
                res[i][j] = std::cmp::min(res[i][j], res[i][k].saturating_add(res[k][j]));
            }
        }
    }

    res
}
