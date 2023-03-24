use crate::UnDirectedTree;
use std::collections::VecDeque;

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
/// Return an array containing the only child of each vertex after decomposition (std::usize::MAX for leaves).
pub fn heavy_light_decomposition(tree: &UnDirectedTree) -> Vec<usize> {
    let mut children = vec![std::usize::MAX; tree.size()];
    decomposition(0, 0, tree, &mut children);

    children
}

/// Returns a function f for the list that performed the HL decomposition of the tree.
/// f(u: usize, v: usize) -> Vec<(usize, usize)>; Returns a sequence of O(log N) intervals representing the path [u, v].
pub fn path_query(tree: &UnDirectedTree) -> impl Fn(usize, usize) -> Vec<(usize, usize)> {
    let children = heavy_light_decomposition(tree);

    let n = children.len();
    let mut index = vec![std::u32::MAX; n];
    let mut cnt = 0;
    let mut group = vec![std::u32::MAX; n];
    // Root is 0.
    group[0] = 0;
    #[derive(Clone)]
    struct LeaderInfo {
        self_index: u32,
        parent_index: u32,
        height: u16,
    }
    let mut leader = vec![LeaderInfo { self_index: 0, parent_index: std::u32::MAX, height: 0 }];
    let mut groups = 1;

    let mut next = VecDeque::new();
    next.push_back(0u32);

    while let Some(i) = next.pop_front() {
        if index[i as usize] == std::u32::MAX {
            let mut now = i as usize;
            while now as u32 != std::u32::MAX {
                for &to in tree.neighbors(now) {
                    if to != children[now] && index[to] == std::u32::MAX {
                        leader.push(LeaderInfo {
                            self_index: to as u32,
                            parent_index: now as u32,
                            height: leader[group[i as usize] as usize].height + 1,
                        });
                        group[to] = groups;
                        groups += 1;
                        next.push_back(to as u32);
                    }
                }
                index[now] = cnt;
                group[now] = group[i as usize];
                cnt += 1;
                now = children[now];
            }
        }
    }

    move |mut u: usize, mut v: usize| -> Vec<(usize, usize)> {
        let mut front = vec![];
        let mut back = vec![];
        while group[u] != group[v] {
            let lu = leader[group[u] as usize].clone();
            let lv = leader[group[v] as usize].clone();

            if lu.height < lv.height {
                back.push((index[lv.self_index as usize] as usize, index[v] as usize));
                v = lv.parent_index as usize;
            } else if lu.height == lv.height {
                back.push((index[lv.self_index as usize] as usize, index[v] as usize));
                v = lv.parent_index as usize;
                front.push((index[u] as usize, index[lu.self_index as usize] as usize));
                u = lu.parent_index as usize;
            } else {
                front.push((index[u] as usize, index[lu.self_index as usize] as usize));
                u = lu.parent_index as usize;
            }
        }

        front.push((index[u] as usize, index[v] as usize));
        front.extend(back.into_iter().rev());
        front
    }
}

#[cfg(test)]
mod tests {
    use crate::{heavy_light_decomposition, UnDirectedTree};

    #[test]
    fn heavy_light_decomposition_test() {
        let edges = vec![(0, 1), (0, 6), (0, 10), (1, 2), (1, 5), (2, 3), (2, 4), (6, 7), (7, 8), (7, 9), (10, 11)];
        let tree = UnDirectedTree::try_from(edges).unwrap();

        let children = heavy_light_decomposition(&tree);
        assert_eq!(
            children,
            vec![1, 2, 3, std::usize::MAX, std::usize::MAX, std::usize::MAX, 7, 8, std::usize::MAX, std::usize::MAX, 11, std::usize::MAX]
        );
    }
}
