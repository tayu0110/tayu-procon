mod rollbackable;

pub use rollbackable::RollbackableUnionFind;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PreviousState {
    AlreadyConnected,
    NotYetConnected,
}

#[derive(Debug, Clone)]
pub struct UnionFind {
    tree: Vec<i32>,
}

impl UnionFind {
    #[inline]
    pub fn new(size: usize) -> Self {
        UnionFind { tree: vec![-1; size] }
    }

    pub fn clear(&mut self) {
        self.tree.fill(-1);
    }

    #[inline]
    pub fn root(&mut self, index: usize) -> usize {
        let mut now = index;
        while self.tree[now] >= 0 {
            now = self.tree[now] as usize;
        }
        let (res, mut now) = (now, index);
        while self.tree[now] >= 0 {
            (self.tree[now], now) = (res as i32, self.tree[now] as usize);
        }
        res
    }

    #[inline]
    pub fn size(&mut self, index: usize) -> usize {
        let root = self.root(index);
        -self.tree[root] as usize
    }

    #[inline]
    pub fn is_same(&mut self, left: usize, right: usize) -> bool {
        self.root(left) == self.root(right)
    }

    #[inline]
    pub fn merge(&mut self, left: usize, right: usize) -> bool {
        let (mut rl, mut rr) = (self.root(left), self.root(right));
        if rl == rr {
            return false;
        }
        if self.tree[rl] > self.tree[rr] {
            (rl, rr) = (rr, rl);
        }
        self.tree[rl] += self.tree[rr];
        self.tree[rr] = rl as i32;
        true
    }
}

/////////////////////////////////////////////////////////////////////////////////////////
/// Weighted UnionFind Tree
/////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub struct AlreadySameGroupError(usize, usize);

impl std::fmt::Display for AlreadySameGroupError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Node {} and Node {} are already belong to the same group.",
            self.0, self.1
        )
    }
}

impl std::error::Error for AlreadySameGroupError {}

/// par\[i\]       : the parent of node i
/// rank\[i\]      : the distance of node i from root
/// potential\[i\] : the potential of the edge between node i and i's parent
pub struct WeightedUnionFind {
    par: Vec<usize>,
    rank: Vec<usize>,
    potential: Vec<i64>,
}

impl WeightedUnionFind {
    pub fn new(size: usize) -> Self {
        Self {
            par: (0..size).collect(),
            rank: vec![0; size],
            potential: vec![0; size],
        }
    }

    pub fn root(&mut self, index: usize) -> usize {
        if self.par[index] == index {
            return index;
        }

        let root = self.root(self.par[index]);
        self.potential[index] += self.potential[self.par[index]];
        self.par[index] = root;
        root
    }

    pub fn is_same(&mut self, l: usize, r: usize) -> bool {
        self.root(l) == self.root(r)
    }

    pub fn merge(
        &mut self,
        l: usize,
        r: usize,
        mut weight: i64,
    ) -> Result<(), AlreadySameGroupError> {
        if self.is_same(l, r) {
            return Err(AlreadySameGroupError(l, r));
        }

        weight = weight + self.weight(l) - self.weight(r);

        let (mut l, mut r) = (self.root(l), self.root(r));
        if self.rank[l] < self.rank[r] {
            std::mem::swap(&mut l, &mut r);
            weight = -weight;
        }

        if self.rank[l] == self.rank[r] {
            self.rank[l] += 1;
        }
        self.par[r] = l;

        self.potential[r] = weight;

        Ok(())
    }

    pub fn weight(&mut self, index: usize) -> i64 {
        let _ = self.root(index);
        self.potential[index]
    }

    pub fn diff(&mut self, l: usize, r: usize) -> i64 {
        self.weight(r) - self.weight(l)
    }
}

#[cfg(test)]
mod tests {
    use super::UnionFind;

    #[test]
    fn unionfind_test() {
        let mut uf = UnionFind::new(4);

        uf.merge(0, 1);
        assert!(uf.is_same(0, 1));
        assert!(!uf.is_same(0, 2));

        uf.merge(0, 2);
        assert!(uf.is_same(1, 2));

        assert_eq!(uf.size(0), 3);
        assert_eq!(uf.size(1), uf.size(0));

        assert_eq!(uf.root(0), uf.root(2));
        assert_ne!(uf.root(0), uf.root(3));
    }

    #[test]
    fn weighted_unionfind_test() {}
}
