use super::{Direction, Tree};

/// If an ancestor earlier than its own rank is searched, std::usize::MAX is returned.  
pub fn nth_ancestor<D: Direction>(tree: &mut Tree<D>) -> impl Fn(usize, usize) -> usize {
    const MAX_RANK_LOG: usize = 25;
    let mut doubling = vec![vec![std::usize::MAX; tree.size()]; MAX_RANK_LOG];

    if tree.par[tree.root()] != std::usize::MAX {
        tree.rebuild();
    }

    for log in 0..MAX_RANK_LOG {
        for now in 0..tree.size() {
            if log == 0 {
                doubling[log][now] = tree.par[now];
            } else {
                let to = doubling[log - 1][now];
                if to != std::usize::MAX {
                    doubling[log][now] = doubling[log - 1][to];
                }
            }
        }
    }

    move |mut now: usize, mut nth: usize| -> usize {
        for log in (0..MAX_RANK_LOG).rev() {
            if nth >= 1 << log {
                now = doubling[log][now];
                nth -= 1 << log;
                if now == std::usize::MAX {
                    break;
                }
            }
        }

        now
    }
}
