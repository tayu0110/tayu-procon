use std::sync::Mutex;

use super::{CycleDetectionError, Directed, Graph};
use ds::FixedRingQueue;

/// Returns the topological sort of a directed graph.  
/// If a cycle is detected, a topological sort cannot be defined, so CycleDetectionError is returned.  
pub fn topological_sort(graph: &Graph<Directed>) -> Result<Vec<usize>, CycleDetectionError> {
    let mut res = vec![];
    let mut ins = vec![0; graph.size()];

    for now in 0..graph.size() {
        for &to in graph.neighbors(now) {
            ins[to] += 1;
        }
    }

    static QUEUE: Mutex<FixedRingQueue<usize>> = Mutex::new(FixedRingQueue::new());
    let mut nt = QUEUE.lock().unwrap();
    nt.clear();
    nt.extend(ins.iter().enumerate().filter(|(_, v)| **v == 0).map(|(i, _)| i));
    while let Some(now) = nt.pop() {
        if ins[now] < 0 {
            continue;
        }
        ins[now] = -1;
        res.push(now);

        for &to in graph.neighbors(now) {
            if ins[to] > 0 {
                ins[to] -= 1;
                if ins[to] == 0 {
                    nt.push(to);
                }
            }
        }
    }

    if res.len() < graph.size() {
        Err(CycleDetectionError)
    } else {
        Ok(res)
    }
}
