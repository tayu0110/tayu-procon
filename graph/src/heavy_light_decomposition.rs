use ds::FixedRingQueue;
use std::{ops::RangeInclusive, sync::Mutex};

/// - **NOT** always from < to.
/// - `from` and `to` of `PathVertex::Range` are the ends of a path, so `to` is **INCLUSIVE**.
/// - `from`, `to` is **NOT the vertex number of the original tree**.<br/>If the original vertex number is needed, you can restore it with `HeavyLightDecomposition::original_index`.
#[derive(Debug, Clone, Copy)]
pub enum PathVertex {
    Range { from: usize, to: usize },
    Edge { from: usize, to: usize },
}

impl PathVertex {
    fn range(from: u32, to: u32) -> PathVertex {
        PathVertex::Range { from: from as usize, to: to as usize }
    }

    fn edge(from: u32, to: u32) -> PathVertex {
        PathVertex::Edge { from: from as usize, to: to as usize }
    }

    pub fn is_range(&self) -> bool {
        let Self::Range { .. } = self else {
            return false;
        };
        true
    }

    pub fn try_into_range_inclusive(self) -> Result<RangeInclusive<usize>, &'static str> {
        let Self::Range { from, to } = self else {
            return Err("Failed to convert to RangeInclusive. This is not PathVertex::Range.");
        };
        Ok(from.min(to)..=from.max(to))
    }
}

/// # Heavy-Light Decomposition
/// - It devides a tree into the O(logN) groups of path by the size of subtree. (`N` is the number of this tree's vertices)
/// - This structure manages the tree vertex numbers as positions on a straight line whose indices are a sequence of points on the path.
/// - To obtain the original tree vertex number, `HeavyLightDecomposition::original_index` must be used.
#[derive(Debug, Clone)]
pub struct HeavyLightDecomposition {
    parent: Vec<u32>,
    leader: Vec<u32>,
    height: Vec<u8>,
    group: Vec<u32>,
    index: Vec<u32>,
    original_index: Vec<u32>,
}

impl HeavyLightDecomposition {
    fn decomposite(now: usize, par: usize, tree: &mut Vec<Vec<usize>>) -> u32 {
        let mut size = 1;
        let mut max = 0;
        let mut child = 0;
        let mut parent = usize::MAX;

        for i in 0..tree[now].len() {
            let to = tree[now][i];
            if to == par {
                parent = i;
                continue;
            }
            let s = Self::decomposite(to, now, tree);
            if s > max {
                child = i;
                max = s;
            }
            size += s;
        }

        tree[now].swap(0, child);
        if parent == 0 {
            tree[now].swap_remove(child);
        } else if parent != usize::MAX {
            tree[now].swap_remove(parent);
        }
        size
    }

    pub fn from_edges(n: usize, edges: impl IntoIterator<Item = (usize, usize)>) -> Self {
        let mut tree = vec![vec![]; n];
        for (from, to) in edges {
            tree[from].push(to);
            tree[to].push(from);
        }

        Self::decomposite(0, 0, &mut tree);

        let mut parent = vec![u32::MAX];
        let mut leader = vec![0];
        let mut height = vec![0];
        let mut group = vec![u32::MAX; n];
        group[0] = 0;

        static QUEUE: Mutex<FixedRingQueue<u32>> = Mutex::new(FixedRingQueue::new());
        let mut next = QUEUE.lock().unwrap();
        next.clear();
        next.push(0u32);
        while let Some(now) = next.pop() {
            if tree[now as usize].is_empty() {
                continue;
            }

            group[tree[now as usize][0]] = group[now as usize];
            next.push(tree[now as usize][0] as u32);

            for &to in tree[now as usize].iter().skip(1) {
                group[to] = leader.len() as u32;
                leader.push(to as u32);
                height.push(height[group[now as usize] as usize] + 1);
                parent.push(now);

                next.push(to as u32);
            }
        }

        let mut cnt = 0;
        let mut index = vec![u32::MAX; n];
        let mut original_index = vec![0; n];
        for &(mut leader) in &leader {
            while leader != u32::MAX {
                index[leader as usize] = cnt;
                original_index[cnt as usize] = leader;
                cnt += 1;
                leader = tree[leader as usize]
                    .first()
                    .map_or(u32::MAX, |a| *a as u32);
            }
        }

        Self { parent, leader, height, group, index, original_index }
    }

    pub fn index(&self, index: usize) -> usize {
        self.index[index] as usize
    }

    pub fn original_index(&self, index: usize) -> usize {
        self.original_index[index] as usize
    }

    pub fn path_iter(
        &self,
        mut from: usize,
        mut to: usize,
    ) -> impl Iterator<Item = PathVertex> + '_ {
        let mut next = None;
        let mut back = vec![];
        let mut finished = false;

        std::iter::from_fn(move || {
            if let Some(p) = next {
                next = None;
                return Some(p);
            }

            while self.group[from] != self.group[to] {
                let (gf, gt) = (self.group[from] as usize, self.group[to] as usize);
                let (lf, lt) = (self.leader[gf] as usize, self.leader[gt] as usize);
                let (pf, pt) = (self.parent[gf] as usize, self.parent[gt] as usize);

                if self.height[gf] > self.height[gt] {
                    let fi = self.index[from];
                    let ti = self.index[lf];
                    from = pf;
                    next = Some(PathVertex::edge(self.index[lf], self.index[pf]));
                    return Some(PathVertex::range(fi, ti));
                } else {
                    let fi = self.index[to];
                    let ti = self.index[lt];
                    back.push(PathVertex::range(ti, fi));
                    back.push(PathVertex::edge(self.index[pt], self.index[lt]));
                    to = pt;
                }
            }

            if !finished {
                let fi = self.index[from];
                let ti = self.index[to];
                finished = true;
                return Some(PathVertex::range(fi, ti));
            }

            back.pop()
        })
    }

    pub fn path_vertex_ranges(
        &self,
        from: usize,
        to: usize,
    ) -> impl Iterator<Item = PathVertex> + '_ {
        self.path_iter(from, to).filter(PathVertex::is_range)
    }

    pub fn lca(&self, mut l: usize, mut r: usize) -> usize {
        while self.group[l] != self.group[r] {
            let (gl, gr) = (self.group[l] as usize, self.group[r] as usize);

            if self.height[gl] > self.height[gr] {
                l = self.parent[gl] as usize;
            } else {
                r = self.parent[gr] as usize;
            }
        }

        if self.index(l) < self.index(r) {
            l
        } else {
            r
        }
    }
}
