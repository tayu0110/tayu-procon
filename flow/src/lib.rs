mod ford_fulkerson;
mod hopcroft_karp;

pub use ford_fulkerson::*;
pub use hopcroft_karp::*;
use numeric::Numeric;

#[derive(Clone, Copy, Debug)]
pub struct Edge<Cap: Numeric> {
    pub to: usize,
    pub cap: Cap,
    pub rev: usize,
}

impl<Cap: Numeric> Edge<Cap> {
    fn new(to: usize, cap: Cap, rev: usize) -> Self {
        Self { to, cap, rev }
    }
}

pub struct Dinic<Cap: Numeric> {
    size: usize,
    level: Vec<i32>,
    iter: Vec<usize>,
    max_flow: Cap,
    start: Option<usize>,
    pub graph: Vec<Vec<Edge<Cap>>>,
}

impl<Cap: Numeric> Dinic<Cap> {
    pub fn new(size: usize) -> Self {
        Self {
            size,
            level: vec![0; size],
            iter: vec![0; size],
            max_flow: Cap::zero(),
            start: None,
            graph: vec![vec![]; size],
        }
    }

    pub fn set_edge(&mut self, from: usize, to: usize, cap: Cap) {
        debug_assert!(cap >= Cap::zero());
        let (rev_from, rev_to) = (self.graph[to].len(), self.graph[from].len());
        self.graph[from].push(Edge::new(to, cap, rev_from));
        self.graph[to].push(Edge::new(from, Cap::zero(), rev_to));
    }

    fn bfs(&mut self, start: usize) {
        self.level = vec![-1; self.size];
        let mut nt: std::collections::VecDeque<(usize, i32)> = std::collections::VecDeque::new();
        nt.push_back((start, 0i32));
        while let Some((now, nd)) = nt.pop_front() {
            if self.level[now] < 0 {
                self.level[now] = nd;
                self.graph[now]
                    .iter()
                    .filter(|e| e.cap > Cap::zero() && self.level[e.to] < 0)
                    .for_each(|e| nt.push_back((e.to, nd + 1)));
            }
        }
    }

    fn dfs(&mut self, now: usize, target: usize, f: Cap) -> Cap {
        if now == target {
            return f;
        }

        let mut i = self.iter[now];
        while i < self.graph[now].len() {
            let e = self.graph[now][i];
            if e.cap > Cap::zero() && self.level[now] < self.level[e.to] {
                let nf = if f < e.cap { f } else { e.cap };
                let d = self.dfs(e.to, target, nf);
                if d > Cap::zero() {
                    self.graph[now][i].cap -= d;
                    self.graph[e.to][e.rev].cap += d;
                    self.iter[now] = i;
                    return d;
                }
            }
            i += 1;
        }
        self.iter[now] = i;
        Cap::zero()
    }

    pub fn flow(&mut self, start: usize, target: usize) -> Cap {
        self.start = Some(start);
        loop {
            self.bfs(start);
            if self.level[target] < 0 {
                break;
            }
            self.iter = vec![0; self.size];
            loop {
                let f = self.dfs(start, target, Cap::max_value());
                if f <= Cap::zero() {
                    break;
                }
                self.max_flow += f;
            }
        }
        self.max_flow
    }

    pub fn min_cut_restoration(&mut self) -> Vec<(usize, Edge<Cap>)> {
        let mut reachable = vec![false; self.size];

        let start = self.start.expect("The start point is ambiguous. Please run Dinic::flow() before Dinic::min_cut_restoration().");

        let mut nt = std::collections::VecDeque::new();
        nt.push_back(start);

        while let Some(now) = nt.pop_front() {
            if reachable[now] {
                continue;
            }
            reachable[now] = true;

            for e in &self.graph[now] {
                if e.cap <= Cap::zero() {
                    continue;
                }
                nt.push_back(e.to);
            }
        }

        let mut res = vec![];
        for i in 0..self.size {
            if !reachable[i] {
                continue;
            }

            for e in &self.graph[i] {
                if !reachable[e.to] {
                    res.push((i, *e));
                }
            }
        }

        res
    }
}
