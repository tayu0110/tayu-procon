#![allow(dead_code)]

pub struct EulerTour {
    vertexes: Vec<usize>,
    edges: Vec<usize>,
}

impl EulerTour {
    fn dfs(now: usize, par: usize, vertexes: &mut Vec<usize>, edges: &mut Vec<usize>, t: &Vec<Vec<(usize, usize)>>) {
        vertexes.push(now);

        for &(to, index) in &t[now] {
            if to != par {
                edges.push(index);
                Self::dfs(to, now, vertexes, edges, t);
                edges.push(index);
            }
        }

        vertexes.push(now);
    }

    pub fn from_edges(size: usize, edges: Vec<(usize, usize)>) -> Self {
        let mut t = vec![vec![]; size];
        for (i, (u, v)) in edges.into_iter().enumerate() {
            t[u].push((v, i));
            t[v].push((u, i));
        }

        let mut vertexes = vec![];
        let mut edges = vec![];
        Self::dfs(0, 0, &mut vertexes, &mut edges, &t);

        Self { vertexes, edges }
    }
}
