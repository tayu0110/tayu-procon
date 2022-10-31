pub const INF: i64 = 0x3f3f3f3f3f3f3f3f;

#[derive(Clone, Copy)]
pub struct Edge {
    pub from: usize,
    pub to: usize,
    pub rev: usize,
    pub cap: i64,
    pub cost: i64
}

pub struct MinCostFlow {
    size: usize,
    edges: Vec<Edge>
}

impl MinCostFlow {
    pub const fn new(size: usize) -> Self {
        Self {
            size,
            edges: vec![]
        }
    }

    pub const fn edges(&self) -> &Vec<Edge> {
        &self.edges
    }

    pub fn add_edge(&mut self, from: usize, to: usize, cap: i64, cost: i64) {
        assert!(from < self.size && to < self.size);

        let (pos, rpos) = (self.edges.len(), self.edges.len()+1);
        self.edges.push(Edge {
            from,
            to,
            rev: rpos,
            cap,
            cost
        });
        self.edges.push(Edge {
            from: to,
            to: from,
            rev: pos,
            cap: 0,
            cost: -cost
        });
    }

    // return (remained cappacity, total cost)
    //      cost == -INF => Graph has Negative Cycle
    pub fn flow(&mut self, from: usize, to: usize, mut cap: i64) -> (i64, i64) {
        let mut res = 0;
        while cap > 0 {
            let (rcap, rcost) = self.bellman_ford(from, to);
            if (rcap, rcost) == (INF, INF) {
                break;
            }
            if (rcap, rcost) == (-INF, -INF) {
                return (cap, -INF);
            }
            cap -= rcap;
            res += rcost;
        }
        (cap, res)
    }

    // ( INF,  INF) => Destination Unreachable
    // (-INF, -INF) => Negative Cycle
    fn bellman_ford(&mut self, from: usize, to: usize) -> (i64, i64) {
        let mut costs = vec![(INF, INF); self.size];
        let mut before = vec![(INF as usize, INF as usize); self.size];
        costs[from] = (INF, 0);

        for i in 0..self.size*2 {
            let mut updated = false;
            for (j, Edge { from, to, rev: _, cap, cost }) in self.edges.iter().enumerate() {
                if *cap > 0 && costs[*from].1 < INF {
                    let (ncap, ncost) = costs[*from];
                    let (_, tcost) = costs[*to];
                    if *cost + ncost < tcost {
                        updated = true;
                        if i < self.size {
                            costs[*to] = (std::cmp::min(ncap, *cap), *cost + ncost);
                            before[*to] = (*from, j);
                        } else {
                            costs[*to] = (-INF, -INF);
                        }
                    }
                }
            }
            if !updated {
                break;
            }
        }
        if costs[to].1 != -INF && costs[to].1 != INF {
            let mut now = to;
            let (rcap, _) = costs[to];
            while now != from {
                let (b, idx) = before[now];
                let rev = self.edges[idx].rev;
                self.edges[idx].cap -= rcap;
                self.edges[rev].cap += rcap;
                now = b;
            }
        }
        costs[to]
    }
}