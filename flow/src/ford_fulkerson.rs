use std::ops::{Add, AddAssign, Sub, SubAssign};
use zero_one::Zero;

pub trait Capacity:
    Sized
    + Clone
    + Copy
    + Zero
    + PartialEq
    + PartialOrd
    + Add<Output = Self>
    + Sub<Output = Self>
    + AddAssign
    + SubAssign
{
}

impl<T> Capacity for T where
    T: Clone
        + Copy
        + Zero
        + PartialEq
        + PartialOrd
        + Add<Output = T>
        + Sub<Output = T>
        + AddAssign
        + SubAssign
{
}

pub struct FordFulkerson<Cap> {
    // to, rev, cap
    t: Vec<Vec<(usize, usize, Cap)>>,
}

impl<Cap: Capacity> FordFulkerson<Cap> {
    pub fn new(size: usize) -> Self {
        Self { t: vec![vec![]; size] }
    }

    pub fn set_edge(&mut self, from: usize, to: usize, cap: Cap) {
        let (fl, tl) = (self.t[from].len(), self.t[to].len());
        self.t[from].push((to, tl, cap));
        self.t[to].push((from, fl, Cap::zero()));
    }

    fn dfs(&mut self, now: usize, dst: usize, f: Option<Cap>, checked: &mut [bool]) -> Option<Cap> {
        if now == dst {
            return f;
        }
        checked[now] = true;

        let len = self.t[now].len();
        for i in 0..len {
            let to = self.t[now][i].0;
            if checked[to] {
                continue;
            }
            if self.t[now][i].2 == Cap::zero() {
                continue;
            }

            let f = match f {
                Some(f) if f < self.t[now][i].2 => f,
                _ => self.t[now][i].2,
            };
            if let Some(f) = self.dfs(to, dst, Some(f), checked) {
                let rev = self.t[now][i].1;
                self.t[to][rev].2 += f;
                self.t[now][i].2 -= f;
                if f != Cap::zero() {
                    return Some(f);
                }
            }
        }

        Some(Cap::zero())
    }

    pub fn flow(&mut self, src: usize, dst: usize) -> Cap {
        let mut res = Cap::zero();
        let mut checked = vec![false; self.t.len()];
        loop {
            let f = self.dfs(src, dst, None, &mut checked).unwrap();

            if f == Cap::zero() {
                break res;
            }

            res += f;
            checked.fill(false);
        }
    }
}
