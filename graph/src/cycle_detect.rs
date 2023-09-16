use super::{Directed, Graph};

/// Detect cycles in a directed graph.
/// If a cycle is successfully detected, return a vertex list for one of cycles.
/// The vertex list is in topological order when one edge of the cycle is cut.
pub fn cycle_detect(graph: &Graph<Directed>) -> Option<Vec<usize>> {
    let size = graph.size();
    // 0: not reached, 1: pending, 2: reached
    let mut state = vec![0u8; size];

    for i in 0..size {
        if state[i] != 2 {
            let mut res = vec![];
            if dfs_for_cycle_detect(i, &mut state, &mut res, &graph).is_some() {
                res.reverse();
                return Some(res);
            }
        }
    }

    None
}
fn dfs_for_cycle_detect(now: usize, state: &mut [u8], stack: &mut Vec<usize>, graph: &Graph<Directed>) -> Option<usize> {
    state[now] = 1;

    for &to in graph.neighbors(now) {
        if state[to] == 2 {
            continue;
        }
        if state[to] == 1 {
            stack.push(now);
            return Some(to);
        }

        if let Some(mut res) = dfs_for_cycle_detect(to, state, stack, graph) {
            if res != usize::MAX {
                stack.push(now);
            }
            if res == now {
                res = usize::MAX;
            }
            return Some(res);
        }
    }

    state[now] = 2;
    None
}
