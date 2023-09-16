use crate::UnDirectedTree;
use ds::FixedRingQueue;
use std::sync::Mutex;

fn decomposition(now: usize, par: usize, tree: &UnDirectedTree, children: &mut Vec<usize>) -> u32 {
    let mut res = 1;
    let mut max = 0;

    for &to in tree.neighbors(now) {
        if par != to {
            let size = decomposition(to, now, tree, children);
            if size > max {
                max = size;
                children[now] = to;
            }
            res += size;
        }
    }

    res
}

/// Perform Heavy-Light Decomposition.
/// Return an array containing the only child of each vertex after decomposition (usize::MAX for leaves).
pub fn heavy_light_decomposition(tree: &UnDirectedTree) -> Vec<usize> {
    let mut children = vec![usize::MAX; tree.size()];
    decomposition(0, 0, tree, &mut children);

    children
}

/// Returns a function f and g for the list that performed the HL decomposition of the tree.
/// f(u: usize, v: usize) -> Vec<(usize, usize)>; Returns a sequence of O(log N) intervals representing the path [u, v].
/// g(v: usize) -> usize; Returns the index of the vertex v.
pub fn path_query(tree: &UnDirectedTree) -> (impl Fn(usize, usize) -> Vec<(usize, usize)>, impl Fn(usize) -> usize) {
    let children = heavy_light_decomposition(tree);

    let n = children.len();
    let mut index = vec![u32::MAX; n];
    let mut cnt = 0;
    let mut group = vec![u32::MAX; n];
    // Root is 0.
    group[0] = 0;
    #[derive(Clone)]
    struct LeaderInfo {
        self_index: u32,
        parent_index: u32,
        height: u16,
    }
    let mut leader = vec![LeaderInfo { self_index: 0, parent_index: u32::MAX, height: 0 }];
    let mut groups = 1;

    static QUEUE: Mutex<FixedRingQueue<u32>> = Mutex::new(FixedRingQueue::new());
    let mut next = QUEUE.lock().unwrap();
    next.clear();
    next.push(0u32);

    while let Some(i) = next.pop() {
        if index[i as usize] == u32::MAX {
            let mut now = i as usize;
            while now as u32 != u32::MAX {
                for &to in tree.neighbors(now).filter(|&&to| to != children[now] && index[to] == u32::MAX) {
                    leader.push(LeaderInfo {
                        self_index: to as u32,
                        parent_index: now as u32,
                        height: leader[group[i as usize] as usize].height + 1,
                    });
                    group[to] = groups;
                    groups += 1;
                    next.push(to as u32);
                }
                index[now] = cnt;
                group[now] = group[i as usize];
                cnt += 1;
                now = children[now];
            }
        }
    }

    let index2 = index.clone();

    (
        move |mut u: usize, mut v: usize| -> Vec<(usize, usize)> {
            if u == v {
                return vec![(index[u] as usize, index[v] as usize)];
            }

            let mut front = vec![];
            let mut back = vec![];
            while group[u] != group[v] {
                let lu = leader[group[u] as usize].clone();
                let lv = leader[group[v] as usize].clone();

                if lu.height <= lv.height {
                    match back.last_mut() {
                        Some((l, _)) if *l == index[v] as usize => *l = index[lv.self_index as usize] as usize,
                        _ => back.push((index[lv.self_index as usize] as usize, index[v] as usize)),
                    }
                    v = lv.parent_index as usize;
                }

                if lu.height >= lv.height {
                    match front.last_mut() {
                        Some((_, r)) if *r == index[lu.self_index as usize] as usize => *r = index[lu.self_index as usize] as usize,
                        _ => front.push((index[u] as usize, index[lu.self_index as usize] as usize)),
                    }
                    u = lu.parent_index as usize;
                }
            }

            match front.last_mut() {
                Some((_, r)) if *r == index[u] as usize => *r = index[v] as usize,
                _ => front.push((index[u] as usize, index[v] as usize)),
            }

            if let Some((bl, br)) = back.pop() {
                match front.last_mut() {
                    Some((_, r)) if *r == br => *r = bl,
                    _ => front.push((bl, br)),
                }
            }
            front.extend(back.into_iter().rev());
            front
        },
        move |v: usize| index2[v] as usize,
    )
}

#[cfg(test)]
mod tests {
    use crate::{heavy_light_decomposition, UnDirectedTree};

    #[test]
    fn heavy_light_decomposition_test() {
        let edges = vec![(0, 1), (0, 6), (0, 10), (1, 2), (1, 5), (2, 3), (2, 4), (6, 7), (7, 8), (7, 9), (10, 11)];
        let tree = UnDirectedTree::try_from(edges).unwrap();

        let children = heavy_light_decomposition(&tree);
        assert_eq!(children, vec![1, 2, 3, usize::MAX, usize::MAX, usize::MAX, 7, 8, usize::MAX, usize::MAX, 11, usize::MAX]);
    }
}
