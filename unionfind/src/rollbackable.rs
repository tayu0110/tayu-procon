use crate::PreviousState;

#[derive(Debug, Clone)]
pub struct RollbackableUnionFind {
    par: Vec<i32>,
    history: Vec<(i32, i32)>,
}

impl RollbackableUnionFind {
    /// Construct a new instance.
    pub fn new(size: usize) -> Self {
        Self { par: vec![-1; size], history: vec![] }
    }

    /// Initialize the state of `self`.  
    /// `self.current_version` also returns to `0`.
    pub fn initialize(&mut self) {
        self.par.fill(-1);
        self.history.clear();
    }

    /// Find the leader of the group `node` belongs to.
    pub fn root(&self, mut node: usize) -> usize {
        while self.par[node] >= 0 {
            node = self.par[node] as usize;
        }
        node
    }

    /// Return the size of the group `node` belongs to.
    ///
    /// # Examples
    /// ```
    /// use unionfind::RollbackableUnionFind;
    ///
    /// let mut uf = RollbackableUnionFind::new(5);
    /// assert_eq!(uf.size(0), 1);
    ///
    /// uf.merge(0, 1);
    /// uf.merge(1, 2);
    /// assert_eq!(uf.size(0), 3);
    ///
    /// uf.merge(3, 4);
    /// assert_eq!(uf.size(3), 2);
    ///
    /// uf.merge(0, 3);
    /// assert_eq!(uf.size(0), 5);
    /// ```
    pub fn size(&self, node: usize) -> usize {
        (-self.par[self.root(node)]) as usize
    }

    /// Merge the groups each of `l` and `r` belong to.
    ///
    /// If `l` and `r` are already in the same group, return `PreviousState::AlreadyConnected`.  
    /// If not, return `PreviousState::NotYetConnected`.
    ///
    /// # Examples
    /// ```rust
    /// use unionfind::{RollbackableUnionFind, PreviousState};
    ///
    /// let mut uf = RollbackableUnionFind::new(2);
    /// assert_eq!(uf.merge(0, 1), PreviousState::NotYetConnected);
    /// assert!(uf.is_same(0, 1));
    /// assert_eq!(uf.merge(0, 1), PreviousState::AlreadyConnected);
    /// ```
    pub fn merge(&mut self, l: usize, r: usize) -> PreviousState {
        let (mut rl, mut rr) = (self.root(l), self.root(r));
        if self.par[rl] > self.par[rr] {
            (rl, rr) = (rr, rl);
        }
        self.history.push((rr as i32, self.par[rr]));
        if rl == rr {
            return PreviousState::AlreadyConnected;
        }

        self.par[rl] += self.par[rr];
        self.par[rr] = rl as i32;
        PreviousState::NotYetConnected
    }

    /// Check whether `l` and `r` belong the same group.
    pub fn is_same(&self, l: usize, r: usize) -> bool {
        self.root(l) == self.root(r)
    }

    /// Check whether `self` is the initial state.  
    /// In other words, `self.current_version()` is equal to `0`.
    pub fn is_initial_state(&self) -> bool {
        self.history.is_empty()
    }

    /// Return the current version of `self`.  
    /// Using the value returned by this method, the set can be restored to its current state with `rollback_version`.
    ///
    /// If `self.is_inisital_state` returns `true`, this method returns `0`.
    pub fn current_version(&self) -> usize {
        self.history.len()
    }

    /// Restore the state of `self` to the time specified by `version`.  
    /// The `version` of the specific set can be obtained with `current_version`.
    ///
    /// # Panics
    /// `version` must be less than or equal to `self.current_version()`.
    ///
    /// # Examples
    /// ```rust
    /// use unionfind::RollbackableUnionFind;
    ///
    /// let mut uf = RollbackableUnionFind::new(5);
    /// uf.merge(0, 1);
    /// uf.merge(1, 2);
    /// let ver = uf.current_version();
    /// uf.merge(2, 3);
    /// assert!(uf.is_same(0, 3));
    /// uf.rollback_version(ver);
    /// assert!(!uf.is_same(0, 3));
    /// ```
    pub fn rollback_version(&mut self, version: usize) {
        if version > self.current_version() {
            panic!("This version '{version}' has not yet arrived.");
        }

        while self.current_version() > version {
            self.undo_once();
        }
    }

    /// Undo the previous `merge`.
    ///
    /// Even if `merge` returned `PreviousState::AlreadyConnected`, the version of `self` increases.  
    /// So when this method is called after `merge` is called for nodes which belong to a same group, this method does not change the state of `self`.
    ///
    /// # Panics
    /// `self.is_initial_state()` must not be equal to `true`.
    ///
    /// # Examples
    /// ```rust
    /// use unionfind::RollbackableUnionFind;
    ///
    /// let mut uf = RollbackableUnionFind::new(3);
    /// uf.merge(0, 1);
    /// uf.merge(0, 1);
    /// uf.merge(1, 2);
    /// assert!(uf.is_same(1, 2));
    /// uf.undo_once();
    /// assert!(!uf.is_same(1, 2));
    /// // the previous `uf.merge(0, 1)` does not change the state of `uf`.
    /// // but it increases the version of `uf`, so `0` and `1` are still connected.
    /// uf.undo_once();
    /// assert!(uf.is_same(0, 1));
    /// // at this point, the first `uf.merge(0, 1)` is canceled.
    /// uf.undo_once();
    /// assert!(!uf.is_same(0, 1));
    /// assert!(uf.is_initial_state());
    /// ```
    pub fn undo_once(&mut self) {
        if self.current_version() == 0 {
            panic!("The current version is 0, so there is no history to restore.");
        }

        let (r, rv) = self.history.pop().unwrap();
        let parent = self.par[r as usize];
        self.par[r as usize] = rv;
        if parent >= 0 {
            self.par[parent as usize] -= rv;
        }
    }

    /// Perform `nth` times undo.
    ///
    /// # Panics
    /// `nth` must be less than or equal to `self.current_version`.
    pub fn undo_nth(&mut self, nth: usize) {
        if self.current_version() < nth {
            panic!("There are not enough histories to restore.");
        }

        for _ in 0..nth {
            self.undo_once();
        }
    }
}
