use std::cmp::{min_by_key, Ordering};

use crate::FixedTree;

pub struct HLDecomposition {
    paths: Vec<HLDPath>,
    group: Vec<u32>,
    pos: Vec<u32>,
}

impl HLDecomposition {
    /// Search the Lowest Common Ancestor of `u` and `v`.
    ///
    /// # Panics
    /// - Both `u < tree.num_vertexes()` and `v < tree.num_vertexes()` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedTree;
    /// type Tree = FixedTree<(), false>;
    ///
    /// let tree = Tree::try_from((8, [(0, 1), (0, 2), (1, 3), (2, 4), (2, 5), (4, 6), (6, 7)])).unwrap();
    /// let hld = tree.heavy_light_decomposition(0);
    ///
    /// assert_eq!(hld.lca(3, 5), 0);
    /// assert_eq!(hld.lca(5, 7), 2);
    /// assert_eq!(hld.lca(6, 7), 6);
    /// assert_eq!(hld.lca(0, 0), 0);
    /// ```
    pub fn lca(&self, mut u: usize, mut v: usize) -> usize {
        assert!(u < self.pos.len() && v < self.pos.len());
        let mut gu = self.group[u] as usize;
        let mut gv = self.group[v] as usize;
        while gu != gv {
            match self.paths[gu].level.cmp(&self.paths[gv].level) {
                Ordering::Less => v = self.paths[gv].parent.unwrap(),
                _ => u = self.paths[gu].parent.unwrap(),
            }
            (gu, gv) = (self.group[u] as usize, self.group[v] as usize);
        }
        min_by_key(u, v, |&i| self.pos[i])
    }

    /// Perform 'Jump on Tree'.
    /// Specifically, this method returns the `nth` vertex that appears on a path starting at `src` and ending at `dst`.
    ///
    /// If such vertexes are not found, return `None`.
    ///
    /// # Panics
    /// - Both `u < tree.num_vertexes()` and `v < tree.num_vertexes()` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedTree;
    /// type Tree = FixedTree<(), false>;
    ///
    /// let tree = Tree::try_from((8, [(0, 1), (0, 2), (1, 3), (2, 4), (2, 5), (4, 6), (6, 7)])).unwrap();
    /// let hld = tree.heavy_light_decomposition(0);
    ///
    /// assert_eq!(hld.jump(3, 5, 3), Some(2));
    /// assert_eq!(hld.jump(5, 7, 10), None);
    /// assert_eq!(hld.jump(6, 7, 1), Some(7));
    /// assert_eq!(hld.jump(0, 0, 0), Some(0));
    /// ```
    pub fn jump(&self, src: usize, dst: usize, nth: usize) -> Option<usize> {
        assert!(src < self.pos.len() && dst < self.pos.len());
        let (mut u, mut v) = (src, dst);
        let mut gu = self.group[u] as usize;
        let mut gv = self.group[v] as usize;
        let mut rem = nth;
        let mut climb = 0;
        while gu != gv {
            match self.paths[gu].level.cmp(&self.paths[gv].level) {
                Ordering::Less => {
                    climb += self.pos[v] as usize + 1;
                    v = self.paths[gv].parent.unwrap();
                }
                _ => {
                    let p = self.pos[u] as usize;
                    if p >= rem {
                        return Some(self.paths[gu].path[p - rem] as usize);
                    }
                    u = self.paths[gu].parent.unwrap();
                    rem -= p + 1;
                }
            }
            (gu, gv) = (self.group[u] as usize, self.group[v] as usize);
        }
        let (pu, pv) = (self.pos[u] as usize, self.pos[v] as usize);
        if u >= v {
            if pu - pv >= rem {
                return Some(self.paths[gu].path[pu - rem] as usize);
            }
            rem -= pu - pv;
        } else {
            climb += pv - pu;
        }

        (climb >= rem).then(|| {
            let mut rem = climb - rem;
            let mut now = dst;
            let mut g = self.group[now] as usize;
            while rem > 0 {
                let p = self.pos[now] as usize;
                if p >= rem {
                    return self.paths[g].path[p - rem] as usize;
                }

                rem -= p + 1;
                now = self.paths[g].parent.unwrap();
                g = self.group[now] as usize;
            }
            now
        })
    }
}

pub struct HLDPath {
    level: u8,
    parent: Option<usize>,
    path: Vec<u32>,
}

fn dfs<W: Clone>(
    now: usize,
    prev: usize,
    paths: &mut Vec<HLDPath>,
    tree: &FixedTree<W, false>,
) -> (usize, HLDPath) {
    let mut res = vec![];
    for e in tree.edges(now).filter(|e| e.to() != prev) {
        res.push(dfs(e.to(), now, paths, tree));
    }

    if res.is_empty() {
        return (
            1,
            HLDPath { level: u8::MAX, parent: None, path: vec![now as u32] },
        );
    }

    let w = res.iter().map(|v| v.0).sum::<usize>() + 1;
    res.sort_unstable_by_key(|p| p.0);

    let (_, mut heavy) = res.pop().unwrap();
    heavy.level = res
        .iter()
        .map(|v| v.1.level - 1)
        .min()
        .unwrap_or(u8::MAX)
        .min(heavy.level);
    heavy.path.push(now as u32);

    paths.extend(res.into_iter().map(|(_, mut path)| {
        path.parent = Some(now);
        path.path.reverse();
        path
    }));
    (w, heavy)
}

impl<W: Clone> FixedTree<W, false> {
    /// Perform Heavy-Light Decomposition assuming `root` as the root of this tree.  
    /// The information after decomposition and operations using it can be performed through the returned `HLDecomposition`.
    ///
    /// # Panics
    /// - `root < self.num_vertexes()` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use cpgraph::FixedTree;
    /// type Tree = FixedTree<(), false>;
    ///
    /// let tree = Tree::try_from((5, [(0, 1), (1, 2), (1, 3), (2, 4)])).unwrap();
    /// let hld = tree.heavy_light_decomposition(0);
    ///
    /// assert_eq!(hld.lca(3, 4), 1);
    /// assert_eq!(hld.lca(1, 4), 1);
    ///
    /// assert_eq!(hld.jump(0, 4, 1), Some(1));
    /// assert_eq!(hld.jump(0, 4, 5), None);
    /// ```
    pub fn heavy_light_decomposition(&self, root: usize) -> HLDecomposition {
        assert!(root < self.num_vertexes());
        let mut paths = vec![];
        let (_, mut heavy) = dfs(root, root, &mut paths, self);
        heavy.path.reverse();
        paths.push(heavy);

        let mut group = vec![0; self.num_vertexes()];
        let mut pos = vec![0; self.num_vertexes()];
        for (i, p) in paths.iter().enumerate() {
            for (j, &v) in p.path.iter().enumerate() {
                group[v as usize] = i as u32;
                pos[v as usize] = j as u32;
            }
        }

        HLDecomposition { paths, group, pos }
    }

    /// Return the closure can perform 'Jump on Tree'.  
    ///
    /// The signature of returned closure is as same as `HLDecomposition::jump`.
    /// 0th argument is the source of path, 1st is the destination, 2nd is the distance of the source.
    ///
    /// If the vertex satisfies conditions specified by arguments is not found, return `None`.
    pub fn jump(&self) -> impl Fn(usize, usize, usize) -> Option<usize> {
        let hld = self.heavy_light_decomposition(0);
        move |src: usize, dst: usize, nth: usize| -> Option<usize> { hld.jump(src, dst, nth) }
    }
}
