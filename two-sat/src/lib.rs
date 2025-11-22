use graph::{scc, DirectedGraph};

pub struct TwoSAT {
    size: usize,
    is_built: bool,
    res: Vec<bool>,
    scc_groups: Vec<usize>,
    graph: DirectedGraph,
}

impl TwoSAT {
    pub fn new(size: usize) -> Self {
        let res = vec![false; size];
        let scc_groups = vec![0; size * 2];
        let graph = DirectedGraph::new(size * 2);
        Self { size, is_built: false, res, scc_groups, graph }
    }

    pub fn add_clause(&mut self, i: usize, f: bool, j: usize, g: bool) {
        assert!(i < self.size && j < self.size);
        self.graph
            .set_edge(2 * i + if f { 0 } else { 1 }, 2 * j + if g { 1 } else { 0 });
        self.graph
            .set_edge(2 * j + if g { 0 } else { 1 }, 2 * i + if f { 1 } else { 0 });
        self.is_built = false;
    }

    pub fn satisfiable(&mut self) -> bool {
        if !self.is_built {
            let groups = scc(&self.graph);
            for (i, v) in groups.into_iter().enumerate() {
                for v in v {
                    self.scc_groups[v] = i;
                }
            }
        }

        for i in 0..self.size {
            if self.scc_groups[2 * i] == self.scc_groups[2 * i + 1] {
                return false;
            }
            self.res[i] = self.scc_groups[2 * i] < self.scc_groups[2 * i + 1];
        }
        true
    }

    pub fn answer(&self) -> &Vec<bool> {
        &self.res
    }
}
