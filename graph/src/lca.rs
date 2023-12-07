use super::{Direction, Tree};
use ds::FixedRingQueue;
use std::sync::Mutex;

/// Returns a closure that finds the Lowest Common Ancestor of the two vertices belonging to the tree.
#[deprecated(
    note = "HeavyLightDecomposition::lca is superior in both speed and memory than this, so you should use it."
)]
pub fn lca<D: Direction>(tree: &mut Tree<D>) -> impl Fn(usize, usize) -> usize {
    const MAX_RANK_LOG: usize = 25;
    let mut doubling = vec![vec![u32::MAX; tree.size()]; MAX_RANK_LOG];
    let mut rank = vec![u32::MAX; tree.size()];

    static QUEUE: Mutex<FixedRingQueue<(usize, u32)>> = Mutex::new(FixedRingQueue::new());
    let mut nt = QUEUE.lock().unwrap();
    nt.clear();
    nt.push((tree.root(), 0));
    while let Some((now, r)) = nt.pop() {
        if rank[now] != u32::MAX {
            continue;
        }
        rank[now] = r;

        let parent = tree.parent(now);
        for &to in tree.neighbors(now).filter(|&&to| to != parent) {
            nt.push((to, r + 1));
        }
    }

    let mut height = 0;
    for log in 0..MAX_RANK_LOG {
        let mut updated = false;
        for now in 0..tree.size() {
            if log == 0 {
                doubling[log][now] = tree.parent(now) as u32;
                updated = true;
            } else {
                let to = doubling[log - 1][now];
                if to != u32::MAX {
                    doubling[log][now] = doubling[log - 1][to as usize];
                    updated = true;
                }
            }
        }

        if !updated {
            height = log + 1;
            break;
        }
    }

    // return the 0-based index of the Most Significant Bit for b.
    // almost as same as bsr instruction. when b is 0, it is UB
    fn bit_scan_reverse(b: u32) -> usize {
        31 - b.leading_zeros() as usize
    }

    move |mut l: usize, mut r: usize| -> usize {
        if rank[l] > rank[r] {
            (l, r) = (r, l);
        }
        if rank[r] > rank[l] {
            let mut diff = rank[r] - rank[l];
            while diff > 0 {
                let log = bit_scan_reverse(diff);
                r = doubling[log][r] as usize;
                diff -= 1 << log;
            }
        }
        if l == r {
            return l;
        }

        for log in (0..height).rev() {
            if doubling[log][l] != doubling[log][r] {
                l = doubling[log][l] as usize;
                r = doubling[log][r] as usize;
            }
        }

        doubling[0][l] as usize
    }
}
