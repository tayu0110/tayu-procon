use crate::FixedTree;

pub struct EulerTourEdge {
    src: usize,
    dst: usize,
    edge_index: usize,
}

impl EulerTourEdge {
    /// The source point of this edge.
    pub fn source(&self) -> usize {
        self.src
    }

    /// The destination point of this edge.
    pub fn destination(&self) -> usize {
        self.dst
    }

    /// The index of this edge.
    pub fn edge_index(&self) -> usize {
        self.edge_index
    }
}

pub struct EulerTour {
    pub(crate) vertexes: Vec<u32>,
    pub(crate) edge_indices: Vec<u32>,
    pub(crate) level: Vec<u32>,
}

impl EulerTour {
    /// Return information of the `nth`-th edge on this Euler Tour.
    pub fn nth_edge(&self, nth: usize) -> EulerTourEdge {
        EulerTourEdge {
            src: self.vertexes[nth] as usize,
            dst: self.vertexes[nth + 1] as usize,
            edge_index: self.edge_indices[nth] as usize,
        }
    }

    /// Return the index of the `nth`-th vertex on this Euler Tour.
    pub fn nth_vertex(&self, nth: usize) -> usize {
        self.vertexes[nth] as usize
    }

    /// Returns the number of edges from the root to each vertex, i.e., the depth of the vertex.  
    ///
    /// The length of the returned slice is the number of vertexes in the Euler Tour,
    /// and the Nth element is the depth of the Nth vertex in the Euler Tour.
    pub fn level(&self) -> &[u32] {
        &self.level
    }

    /// Returns information on all edges included in the Euler Tour, starting from the front.
    pub fn edges(&self) -> impl ExactSizeIterator<Item = EulerTourEdge> + '_ {
        self.vertexes
            .windows(2)
            .zip(self.level.iter())
            .map(|(v, l)| EulerTourEdge {
                src: v[0] as usize,
                dst: v[1] as usize,
                edge_index: *l as usize,
            })
    }
}

fn dfs<W: Clone>(
    now: usize,
    prev: usize,
    vertexes: &mut Vec<u32>,
    edge_indices: &mut Vec<u32>,
    level: &mut [u32],
    tree: &FixedTree<W, false>,
) {
    vertexes.push(now as u32);
    for e in tree.edges(now).filter(|e| e.to() != prev) {
        edge_indices.push(e.index() as u32);
        level[e.to()] = level[now] + 1;
        dfs(e.to(), now, vertexes, edge_indices, level, tree);
        edge_indices.push(e.index() as u32);
        vertexes.push(now as u32);
    }
}

impl<W: Clone> FixedTree<W, false> {
    /// Returns the Euler Tour of this tree, assuming `root` to be the root of this tree.  
    /// The Euler Tour information can be accessed from the returned `EulerTour`.
    pub fn euler_tour(&self, root: usize) -> EulerTour {
        let mut vertexes = vec![];
        let mut edge_indices = vec![];
        let mut level = vec![0; self.num_vertexes()];
        dfs(
            root,
            root,
            &mut vertexes,
            &mut edge_indices,
            &mut level,
            self,
        );

        EulerTour { vertexes, edge_indices, level }
    }
}
