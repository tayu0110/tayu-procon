use static_modint::{Modulo, StaticModint};
use std::{
    fmt::Debug,
    marker::PhantomData,
    ops::{Add, Mul},
};
use zero_one::{One, Zero};

pub trait MapMonoid {
    type E: Clone;
    type Act: Clone;

    fn op(l: Self::E, r: Self::E) -> Self::E;
    fn e() -> Self::E;
    fn id() -> Self::Act;
    fn map(act: Self::Act, elem: Self::E) -> Self::E;
    fn composite(l: Self::Act, r: Self::Act) -> Self::Act;
}

#[derive(Clone)]
pub struct LazySegtree<M: MapMonoid> {
    n: usize,
    size: usize,
    log: usize,
    tree: Vec<M::E>,
    lazy: Vec<M::Act>,
}

impl<M: MapMonoid> LazySegtree<M> {
    pub fn new(size: usize) -> Self { LazySegtree::from_vec(&vec![M::e(); size]) }

    pub fn from_vec(v: &Vec<M::E>) -> Self {
        let n = v.len();
        let size = n.next_power_of_two();
        let log = size.trailing_zeros() as usize;
        let mut tree = vec![M::e(); size * 2];
        let lazy = vec![M::id(); size * 2];
        tree.iter_mut()
            .skip(size)
            .zip(v.iter().cloned())
            .for_each(|(t, w)| *t = w);
        for i in (1..size).rev() {
            tree[i] = M::op(tree[i * 2].clone(), tree[i * 2 + 1].clone());
        }
        Self { n, size, log, tree, lazy }
    }
    pub fn set(&mut self, idx: usize, val: M::E) {
        assert!(idx < self.n);
        let idx = idx + self.size;
        for i in (1..self.log + 1).rev() {
            self.push(idx >> i);
        }
        self.tree[idx] = val;
        for i in 1..=self.log {
            self.update(idx >> i);
        }
    }
    // Get the value of a single point whose index is idx.
    pub fn get(&mut self, idx: usize) -> M::E {
        assert!(idx < self.n);
        let idx = idx + self.size;
        for i in (1..self.log + 1).rev() {
            self.push(idx >> i);
        }
        self.tree[idx].clone()
    }
    // Get the result of applying the operation to the interval [l, r).
    pub fn prod(&mut self, l: usize, r: usize) -> M::E {
        assert!(l <= r && r <= self.n);
        if l == r {
            return M::e();
        }
        let (mut l, mut r) = (l + self.size, r + self.size);
        for i in (1..self.log + 1).rev() {
            if ((l >> i) << i) != l {
                self.push(l >> i);
            }
            if ((r >> i) << i) != r {
                self.push(r >> i);
            }
        }
        let (mut sml, mut smr) = (M::e(), M::e());
        while l < r {
            if (l & 1) != 0 {
                sml = M::op(sml, self.tree[l].clone());
                l += 1;
            }
            if (r & 1) != 0 {
                r -= 1;
                smr = M::op(self.tree[r].clone(), smr);
            }
            l >>= 1;
            r >>= 1;
        }
        M::op(sml, smr)
    }
    pub fn all_prod(&self) -> M::E { self.tree[1].clone() }
    // Apply val to a point whose index is idx.
    pub fn apply(&mut self, idx: usize, val: M::Act) {
        assert!(idx < self.n);
        let idx = idx + self.size;
        for i in (1..self.log + 1).rev() {
            self.push(idx >> i);
        }
        self.tree[idx] = M::map(val, self.tree[idx].clone());
        for i in 1..=self.log {
            self.update(idx >> i);
        }
    }
    // Apply val to the interval [l, r).
    pub fn apply_range(&mut self, l: usize, r: usize, val: M::Act) {
        assert!(l <= r && r <= self.n);
        if l == r {
            return;
        }
        let (l, r) = (l + self.size, r + self.size);
        for i in (1..self.log + 1).rev() {
            if ((l >> i) << i) != l {
                self.push(l >> i);
            }
            if ((r >> i) << i) != r {
                self.push((r - 1) >> i);
            }
        }
        let (mut a, mut b) = (l, r);
        while a < b {
            if (a & 1) != 0 {
                self.all_apply(a, val.clone());
                a += 1;
            }
            if (b & 1) != 0 {
                b -= 1;
                self.all_apply(b, val.clone());
            }
            a >>= 1;
            b >>= 1;
        }
        for i in 1..=self.log {
            if ((l >> i) << i) != l {
                self.update(l >> i);
            }
            if ((r >> i) << i) != r {
                self.update((r - 1) >> i);
            }
        }
    }
    fn update(&mut self, idx: usize) {
        self.tree[idx] = M::op(self.tree[idx * 2].clone(), self.tree[idx * 2 + 1].clone());
    }
    fn all_apply(&mut self, idx: usize, val: M::Act) {
        self.tree[idx] = M::map(val.clone(), self.tree[idx].clone());
        if idx < self.size {
            self.lazy[idx] = M::composite(val, self.lazy[idx].clone());
        }
    }
    fn push(&mut self, idx: usize) {
        self.all_apply(idx * 2, self.lazy[idx].clone());
        self.all_apply(idx * 2 + 1, self.lazy[idx].clone());
        self.lazy[idx] = M::id();
    }
}
impl<M: MapMonoid> Debug for LazySegtree<M>
where
    M: MapMonoid,
    M::E: Debug,
    M::Act: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (mut tree, mut lazy, mut l, mut r) = (vec![], vec![], 1, 2);
        while r < self.tree.len() {
            let (mut nd, mut nlz) = (vec![], vec![]);
            for i in l..r {
                nd.push(&self.tree[i]);
                nlz.push(&self.lazy[i]);
            }
            tree.push(nd);
            lazy.push(nlz);
            l <<= 1;
            r <<= 1;
        }
        write!(f, "tree: {:?}\nlz: {:?}", tree, lazy)
    }
}

pub struct RangeAddRangeSumQuery<T>(PhantomData<fn() -> T>);

impl<T> RangeAddRangeSumQuery<T>
where
    T: Zero + One + Clone + Add<Output = T> + Mul<Output = T>,
{
    pub fn new(size: usize) -> LazySegtree<Self> {
        LazySegtree::from_vec(&vec![(T::zero(), T::one()); size])
    }
}

impl<T> MapMonoid for RangeAddRangeSumQuery<T>
where
    T: Zero + One + Clone + Add<Output = T> + Mul<Output = T>,
{
    type E = (T, T);
    type Act = T;

    fn e() -> Self::E { (T::zero(), T::zero()) }
    fn op(l: Self::E, r: Self::E) -> Self::E { (l.0 + r.0, l.1 + r.1) }
    fn id() -> Self::Act { T::zero() }
    fn composite(l: Self::Act, r: Self::Act) -> Self::Act { l + r }
    fn map(act: Self::Act, elem: Self::E) -> Self::E { (elem.0 + act * elem.1.clone(), elem.1) }
}

pub struct RangeAddRangeMaximumQuery;

impl RangeAddRangeMaximumQuery {
    pub fn new(size: usize) -> LazySegtree<Self> { LazySegtree::from_vec(&vec![0; size]) }
}

impl MapMonoid for RangeAddRangeMaximumQuery {
    type E = i64;
    type Act = i64;

    fn e() -> Self::E { i64::MIN }
    fn op(l: Self::E, r: Self::E) -> Self::E { l.max(r) }
    fn id() -> Self::Act { 0 }
    fn composite(l: Self::Act, r: Self::Act) -> Self::Act { l + r }
    fn map(act: Self::Act, elem: Self::E) -> Self::E { act + elem }
}

pub struct RangeAddRangeMinimumQuery;

impl RangeAddRangeMinimumQuery {
    pub fn new(size: usize) -> LazySegtree<Self> { LazySegtree::from_vec(&vec![0; size]) }
}

impl MapMonoid for RangeAddRangeMinimumQuery {
    type E = i64;
    type Act = i64;

    fn e() -> Self::E { i64::MAX }
    fn op(l: Self::E, r: Self::E) -> Self::E { l.min(r) }
    fn id() -> Self::Act { 0 }
    fn composite(l: Self::Act, r: Self::Act) -> Self::Act { l + r }
    fn map(act: Self::Act, elem: Self::E) -> Self::E { act + elem }
}

pub struct RangeAffineRangeSum<M: Modulo>(PhantomData<fn() -> M>);

impl<M: Modulo> RangeAffineRangeSum<M> {
    pub fn new(a: Vec<StaticModint<M>>) -> LazySegtree<Self> {
        let a = a.into_iter().map(|v| (v, StaticModint::one())).collect();
        LazySegtree::from_vec(&a)
    }
}

impl<M: Modulo> MapMonoid for RangeAffineRangeSum<M> {
    type E = (StaticModint<M>, StaticModint<M>);
    type Act = (StaticModint<M>, StaticModint<M>);

    fn e() -> Self::E { (StaticModint::zero(), StaticModint::zero()) }
    fn op(l: Self::E, r: Self::E) -> Self::E { (l.0 + r.0, l.1 + r.1) }
    fn id() -> Self::Act { (StaticModint::one(), StaticModint::zero()) }
    fn composite(l: Self::Act, r: Self::Act) -> Self::Act { (l.0 * r.0, l.0 * r.1 + l.1) }
    fn map(act: Self::Act, elem: Self::E) -> Self::E { (act.0 * elem.0 + act.1 * elem.1, elem.1) }
}

pub struct RangeFlipRangeLongestTerm;

impl RangeFlipRangeLongestTerm {
    pub fn new(v: &[bool]) -> LazySegtree<Self> {
        LazySegtree::from_vec(
            &v.into_iter()
                .map(|&f| {
                    let f = f as u32;
                    (f, f, f, 1, 1 - f, 1 - f, 1 - f)
                })
                .collect(),
        )
    }
}

impl MapMonoid for RangeFlipRangeLongestTerm {
    type E = (u32, u32, u32, u32, u32, u32, u32);
    type Act = bool;

    fn e() -> Self::E { (0, 0, 0, 0, 1, 1, 1) }
    fn op(l: Self::E, r: Self::E) -> Self::E {
        let (rm, rl, rr, rt, rm0, rl0, rr0) = r;
        let (m, l, r, t, m0, l0, r0) = l;
        (
            rm.max(m).max(r + rl),
            if l == t { l + rl } else { l },
            if rr == rt { rr + r } else { rr },
            t + rt,
            rm0.max(m0).max(r0 + rl0),
            if l0 == t { l0 + rl0 } else { l0 },
            if rr0 == rt { rr0 + r0 } else { rr0 },
        )
    }
    fn id() -> Self::Act { false }
    fn composite(l: Self::Act, r: Self::Act) -> Self::Act { l ^ r }
    fn map(act: Self::Act, elem: Self::E) -> Self::E {
        if !act {
            return elem;
        }
        let (m, l, r, t, m0, l0, r0) = elem;
        (m0, l0, r0, t, m, l, r)
    }
}
