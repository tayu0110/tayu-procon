use super::{Direction, Tree};

/// Returns a closure that finds the Lowest Common Ancestor of the two vertices belonging to the tree.
pub fn lca<D: Direction>(tree: &mut Tree<D>) -> impl Fn(usize, usize) -> usize {
    const MAX_RANK_LOG: usize = 25;
    let mut doubling = vec![vec![std::usize::MAX; tree.size()]; MAX_RANK_LOG];
    let mut rank = vec![std::usize::MAX; tree.size()];

    let mut nt = std::collections::VecDeque::new();
    nt.push_back((tree.root(), 0));
    while let Some((now, r)) = nt.pop_front() {
        if rank[now] != std::usize::MAX {
            continue;
        }
        rank[now] = r;

        let parent = tree.parent(now);
        for &to in tree.neighbors(now).filter(|&&to| to != parent) {
            nt.push_back((to, r + 1));
        }
    }

    for log in 0..MAX_RANK_LOG {
        for now in 0..tree.size() {
            if log == 0 {
                doubling[log][now] = tree.parent(now);
            } else {
                let to = doubling[log - 1][now];
                if to != std::usize::MAX {
                    doubling[log][now] = doubling[log - 1][to];
                }
            }
        }
    }

    move |mut l: usize, mut r: usize| -> usize {
        if rank[l] > rank[r] {
            std::mem::swap(&mut l, &mut r);
        }
        if rank[r] > rank[l] {
            let mut diff = rank[r] - rank[l];
            for log in (0..MAX_RANK_LOG).rev() {
                if diff >= 1 << log {
                    r = doubling[log][r];
                    diff -= 1 << log;
                }
            }
        }
        if l == r {
            return l;
        }

        for log in (0..MAX_RANK_LOG).rev() {
            if doubling[log][l] != doubling[log][r] {
                l = doubling[log][l];
                r = doubling[log][r];
            }
        }

        doubling[0][l]
    }
}
