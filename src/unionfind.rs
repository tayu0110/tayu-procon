pub struct UnionFind {
    tree: Vec<i32>
}

#[allow(dead_code)]
impl UnionFind {
    pub fn new(size: usize) -> Self {
        UnionFind { tree: vec![-1; size] }
    }

    pub fn root(&self, index: usize) -> usize {
        if self.tree[index] < 0 {
            index
        } else {
            self.root(self.tree[index] as usize)
        }
    }

    pub fn size(&self, index: usize) -> usize {
        -self.tree[self.root(index)] as usize
    }

    pub fn is_same(&self, left: usize, right: usize) -> bool {
        self.root(left) == self.root(right)
    }

    pub fn merge(&mut self, left: usize, right: usize) -> bool {
        let (mut rl, mut rr) = (self.root(left), self.root(right));
        if rl == rr {
            return false;
        }
        if self.tree[rl] > self.tree[rr] {
            std::mem::swap(&mut rl, &mut rr);
        }
        self.tree[rl] += self.tree[rr];
        self.tree[rr] = rl as i32;
        true
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
}