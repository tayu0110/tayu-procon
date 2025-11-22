use crate::Capacity;

pub struct FordFulkerson<Cap> {
    // to, rev, cap
    t: Vec<Vec<(usize, usize, Cap)>>,
}

impl<Cap: Capacity> FordFulkerson<Cap> {
    pub fn new(size: usize) -> Self {
        Self { t: vec![vec![]; size] }
    }

    pub fn add_edge(&mut self, from: usize, to: usize, cap: Cap) {
        let (fl, tl) = (self.t[from].len(), self.t[to].len());
        self.t[from].push((to, tl, cap));
        self.t[to].push((from, fl, Cap::default()));
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
            if self.t[now][i].2 == Cap::default() {
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
                if f != Cap::default() {
                    return Some(f);
                }
            }
        }

        Some(Cap::default())
    }

    pub fn flow(&mut self, src: usize, dst: usize) -> Cap {
        let mut res = Cap::default();
        let mut checked = vec![false; self.t.len()];
        loop {
            let f = self.dfs(src, dst, None, &mut checked).unwrap();

            if f == Cap::default() {
                break res;
            }

            res += f;
            checked.fill(false);
        }
    }
}
