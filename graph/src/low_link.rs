use super::{Direction, Graph};

/// Detect bridges in the graph.  
/// The detected bridges are returned as a list of tuples of vertices at both ends.  
/// The elements of a tuple are always placed with the directed edge source in front and destination behind.  
pub fn low_link<D: Direction>(graph: &Graph<D>) -> Vec<(usize, usize)> {
    let mut ord = vec![std::usize::MAX; graph.size()];
    let mut low = vec![std::usize::MAX; graph.size()];

    let mut next_ord = 0;
    let mut res = vec![];
    for start in 0..graph.size() {
        if ord[start] == std::usize::MAX {
            next_ord = dfs_for_lowlink(start, std::usize::MAX, next_ord, &mut ord, &mut low, &mut res, &graph);
        }
    }
    res
}

fn dfs_for_lowlink<D: Direction>(now: usize, par: usize, now_ord: usize, ord: &mut Vec<usize>, low: &mut Vec<usize>, res: &mut Vec<(usize, usize)>, graph: &Graph<D>) -> usize {
    ord[now] = now_ord;
    low[now] = ord[now];

    let mut next_ord = now_ord + 1;
    for &to in graph.neighbors(now) {
        if ord[to] == std::usize::MAX {
            next_ord = dfs_for_lowlink(to, now, next_ord, ord, low, res, graph);
            low[now] = std::cmp::min(low[now], low[to]);
            if ord[now] < low[to] {
                res.push((now, to));
            }
        }
        if to != par {
            low[now] = std::cmp::min(low[now], ord[to]);
        }
    }

    next_ord
}
