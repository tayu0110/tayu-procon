use std::{
    marker::PhantomData,
    ops::{Bound, RangeBounds},
    usize,
};

pub trait AbelianGroup {
    type G;
    fn e() -> Self::G;
    fn op(l: &Self::G, r: &Self::G) -> Self::G;
    fn inv(g: &Self::G) -> Self::G;
}

#[derive(Debug, Clone)]
pub struct FenwickTree<G: AbelianGroup> {
    tree: Vec<G::G>,
}

impl<G: AbelianGroup> FenwickTree<G> {
    /// Constructor.  
    /// Generate a Fenwick Tree initialized by `G::e()`.
    pub fn new(size: usize) -> Self {
        Self { tree: (0..=size).map(|_| G::e()).collect() }
    }

    /// Return the length of managed sequence.
    pub fn len(&self) -> usize {
        // To process the queries in 1-index,
        // the internal array length is 1 longer than the actual sequence.
        self.tree.len() - 1
    }

    /// Check if `self.len() == 0` is `true`.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Add `val` to the `idx`-th element of managed sequence.  
    /// The target element is updated by `G::op()`.
    ///
    /// # Examples
    /// ```rust
    /// use fenwick_tree::{FenwickTree, Addition};
    ///
    /// let mut ft = FenwickTree::<Addition<i32>>::from([2, 3, 4]);
    /// assert_eq!(ft.fold(..), 9);
    /// assert_eq!(ft.fold(0..1), 2);
    /// ft.add(0, 1);
    /// assert_eq!(ft.fold(..), 10);
    /// assert_eq!(ft.fold(0..1), 3);
    /// ```
    pub fn add(&mut self, at: usize, val: G::G) {
        let mut at = at + 1;
        while at < self.tree.len() {
            self.tree[at] = G::op(&self.tree[at], &val);
            at += at & at.wrapping_neg();
        }
    }

    fn fold_to(&self, to: usize) -> G::G {
        if to == 0 {
            return G::e();
        }
        if to == self.tree.len() {
            return G::op(&G::e(), self.tree.last().unwrap());
        }
        let mut r = to;
        let mut res = G::e();
        while r > 0 {
            res = G::op(&res, &self.tree[r]);
            r -= r & r.wrapping_neg();
        }
        res
    }

    /// Fold the elements in the `range` of the sequence.  
    /// If the length of the interval indicated by `range` is not positive, return `G::e()`.
    ///
    /// # Constraint
    /// - If `G` is not implemented correctly as a abelian group, this method may return meaningless results or panic.  
    ///   Examples: overflow in integer addition, division by zero or truncated division in integer multiplication.
    ///
    /// # Panics
    /// - The `range` must point within the range of the managed sequence.
    ///
    /// # Examples
    /// ```rust
    /// use fenwick_tree::{FenwickTree, Addition};
    ///
    /// let mut ft = FenwickTree::<Addition<i32>>::from([1, 2, 3]);
    /// assert_eq!(ft.fold(..), 6);
    /// assert_eq!(ft.fold(..2), 3);
    /// assert_eq!(ft.fold(1..), 5);
    /// ```
    pub fn fold(&self, range: impl RangeBounds<usize>) -> G::G {
        let si = match range.start_bound() {
            Bound::Included(&0) | Bound::Unbounded => 0,
            Bound::Excluded(&usize::MAX) => panic!("FenwickTree::fold : index out of range"),
            Bound::Included(&a) => a,
            Bound::Excluded(&a) => a + 1,
        };
        let ei = match range.end_bound() {
            Bound::Included(&a) => a + 1,
            Bound::Excluded(&a) => a,
            Bound::Unbounded => self.len(),
        };
        assert!(
            si <= self.len() && ei <= self.len(),
            "FenwickTree::fold : index out of range"
        );
        if si >= ei {
            return G::e();
        }
        G::op(&self.fold_to(ei), &G::inv(&self.fold_to(si)))
    }

    /// Return `at`-th element of managed sequence.  
    /// This method is equivalent to `self.fold(at..at + 1)`.
    ///
    /// If `at < self.len()` is not satisfied, return `None`.
    ///
    /// # Examples
    /// ```rust
    /// use fenwick_tree::{FenwickTree, Addition};
    ///
    /// let mut ft = FenwickTree::<Addition<i32>>::from([1, 2, 3]);
    /// assert_eq!(ft.get(0), Some(1));
    /// assert_eq!(ft.get(1), Some(2));
    /// assert_eq!(ft.get(2), Some(3));
    /// // index out of range
    /// assert_eq!(ft.get(3), None);
    /// ```
    pub fn get(&self, at: usize) -> Option<G::G> {
        (at < self.len()).then(|| self.fold(at..at + 1))
    }

    /// Set `at`-th element as `val`.  
    /// This method is equivalent to `self.add(at, G::op(&val, &G::inv(&now)))`.
    ///
    /// # Panics
    /// - `at < self.len()` must be satisfied.
    ///
    /// # Examples
    /// ```rust
    /// use fenwick_tree::{FenwickTree, Addition};
    ///
    /// let mut ft = FenwickTree::<Addition<i32>>::new(3);
    /// ft.set(0, 1);
    /// // if coumment out the following, panic here !
    /// // ft.set(3, 2);
    /// ```
    pub fn set(&mut self, at: usize, val: G::G) {
        let now = self.get(at).expect("FenwickTree::set : index out of range");
        self.add(at, G::op(&val, &G::inv(&now)));
    }

    /// Find the maximum `pos` that satisfies `pred(&self.fold(0..pos)) == true`.
    ///
    /// # Constraint
    /// - For the result of `pred(&self.fold(0..pos))`,
    ///   all elements of the head of the managed sequence must be `true` and all elements of the tail must be `false`.
    /// - Each the length of `true` or `false` intervals may be 0. In this case, results are `0` or `self.len()`, respectively.
    /// ```ignore
    /// |<-- pred(&self.fold(..pos)) == true -->|<-- pred(&self.fold(..pos)) == false -->|
    /// |0 1 2 3 ...                            |pos pos+1 pos+2 ...         self.len()-1|self.len()
    /// ```
    ///
    /// # Examples
    /// ```rust
    /// use fenwick_tree::{FenwickTree, Addition};
    ///
    /// let mut ft = FenwickTree::<Addition<i32>>::from([1, 0, 5, 2, 4, 3]);
    /// assert_eq!(ft.partition_point(|&s| s < 3), 2);
    /// assert_eq!(ft.partition_point(|&s| s <= 1), 2);
    /// assert_eq!(ft.partition_point(|&s| s < i32::MAX), ft.len());
    /// assert_eq!(ft.partition_point(|&s| s < i32::MIN), 0);
    /// ```
    pub fn partition_point(&self, mut pred: impl FnMut(&G::G) -> bool) -> usize {
        let mut val = G::e();
        let mut n = self.tree.len().next_power_of_two();
        let mut pos = 0;
        while n > 0 {
            if pos + n < self.tree.len() {
                let nv = G::op(&val, &self.tree[pos + n]);
                if pred(&nv) {
                    pos += n;
                    val = nv;
                }
            }
            n >>= 1;
        }
        pos
    }
}

impl<G: AbelianGroup> From<Vec<G::G>> for FenwickTree<G> {
    fn from(mut value: Vec<G::G>) -> Self {
        value.insert(0, G::e());
        for i in (1..value.len()).rev() {
            let mut at = i;
            while {
                at += at & at.wrapping_neg();
                at < value.len()
            } {
                value[at] = G::op(&value[at], &value[i]);
            }
        }

        Self { tree: value }
    }
}

impl<G: AbelianGroup> From<&[G::G]> for FenwickTree<G>
where
    G::G: Clone,
{
    fn from(value: &[G::G]) -> Self {
        Self::from(value.to_vec())
    }
}

impl<G: AbelianGroup, const N: usize> From<[G::G; N]> for FenwickTree<G> {
    fn from(value: [G::G; N]) -> Self {
        Self::from(Vec::from(value))
    }
}

impl<G: AbelianGroup> FromIterator<G::G> for FenwickTree<G> {
    fn from_iter<T: IntoIterator<Item = G::G>>(iter: T) -> Self {
        Self::from(iter.into_iter().collect::<Vec<_>>())
    }
}

pub struct Addition<T>(PhantomData<T>);

macro_rules! impl_addition {
    ( $( $t:ty ),* ) => {
        $(
            impl AbelianGroup for Addition<$t> {
                type G = $t;
                fn e() -> Self::G {
                    0
                }
                fn op(l: &Self::G, r: &Self::G) -> Self::G {
                    l.wrapping_add(*r)
                }
                fn inv(g: &Self::G) -> Self::G {
                    g.wrapping_neg()
                }
            }
        )*
    };
}
impl_addition!(i8, i16, i32, i64, i128, isize, u8, u16, u32, u64, u128, usize);
