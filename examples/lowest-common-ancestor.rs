// use tayu_procon::{
//     scan,
//     graph::{
//         UnDirectedTree, lca
//     }
// };

#![allow(dead_code)]

use graph::{
    UnDirectedTree, lca
};

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(n: usize, q: usize, p: [usize; n-1], q: [(usize, usize); q]);
    let p = vec![std::usize::MAX].into_iter().chain(p.into_iter()).collect();

    let mut tree = UnDirectedTree::from_par_list(p).unwrap();

    let lca = lca(&mut tree);

    for (u, v) in q {
        writeln!(out, "{}", lca(u, v)).unwrap();
    }
}

mod iolib {
use std::cell::RefCell;
use std::io::{
    Read, BufRead,
    Error
};
use std::str::SplitWhitespace;
use std::thread_local;

thread_local! {
    static BUF_SPLIT_WHITESPACE: RefCell<SplitWhitespace<'static>> = RefCell::new("".split_whitespace());
}

#[inline]
fn refill_buffer(interactive: bool) -> Result<(), Error> {
    let mut s = String::new();
    
    if cfg!(debug_assertions) || interactive {
        std::io::stdin().lock().read_line(&mut s)?;
    } else {
        std::io::stdin().lock().read_to_string(&mut s)?;
    }

    BUF_SPLIT_WHITESPACE.with(|buf_str| {
        *buf_str.borrow_mut() = Box::leak(s.into_boxed_str()).split_whitespace();
        Ok(())
    })
}

#[inline]
pub fn scan_string(interactive: bool) -> &'static str {
    BUF_SPLIT_WHITESPACE.with(|buf_str| {
        if let Some(s) = buf_str.borrow_mut().next() {
            return s;
        }

        refill_buffer(interactive).unwrap();

        if let Some(s) = buf_str.borrow_mut().next() {
            return s;
        }

        unreachable!("Read Error: No input items.");
    })
}

#[macro_export]
macro_rules! scan {
    // Terminator
    ( @interactive : $interactive:literal ) => {};
    // Terminator
    ( @interactive : $interactive:literal, ) => {};
    // Vec<Vec<....>>
    ( @interactive : $interactive:literal, $v: ident : [ [ $( $inner:tt )+ ] ; $len:expr ]) => {
        let $v = {
            let len = $len;
            (0..len).fold(vec![], |mut v, _| {
                $crate::scan!(@interactive: $interactive, w: [ $( $inner )+ ]);
                v.push(w);
                v
            })
        };
    };
    // Vec<Vec<....>>, ......
    ( @interactive : $interactive:literal, $v: ident : [ [ $( $inner:tt )+ ] ; $len:expr ] , $( $rest:tt )* ) => {
        $crate::scan!(@interactive: $interactive, [ [ $( $inner )+ ] ; $len ]);
        $crate::scan!(@interactive: $interactive, $( $rest )*);
    };
    // Vec<$t>
    ( @interactive : $interactive:literal, $v:ident : [ $t:tt ; $len:expr ]) => {
        let $v = {
            let len = $len;
            (0..len).map(|_| { $crate::scan!(@interactive: $interactive, $v : $t); $v }).collect::<Vec<_>>()
        };
    };
    // Vec<$t>, .....
    ( @interactive : $interactive:literal, $v:ident : [ $t:tt ; $len:expr ] , $( $rest:tt )* ) => {
        let $v = {
            let len = $len;
            (0..len).map(|_| { $crate::scan!(@interactive: $interactive, $v : $t); $v }).collect::<Vec<_>>()
        };
        $crate::scan!(@interactive: $interactive, $( $rest )*);
    };
    // Expand tuple
    ( @interactive : $interactive:literal, @expandtuple, ( $t:tt )) => {
        { let tmp = $crate::iolib::scan_string($interactive).parse::<$t>().unwrap(); tmp }
    };
    // Expand tuple
    ( @interactive : $interactive:literal, @expandtuple, ( $t:tt $( , $rest:tt )* ) ) => {
        (
            $crate::scan!(@interactive: $interactive, @expandtuple, ( $t )),
            $( $crate::scan!(@interactive: $interactive, @expandtuple, ( $rest )), )*
        )
    };
    // let $v: ($t, $u, ....) = (.......)
    ( @interactive : $interactive:literal, $v:ident : ( $( $rest:tt )* ) ) => {
        let $v = $crate::scan!(@interactive: $interactive, @expandtuple, ( $( $rest )* ));
    };
    // let $v: $t = ......
    ( @interactive : $interactive:literal, $v:ident : $t:ty ) => {
        let $v = $crate::iolib::scan_string($interactive).parse::<$t>().unwrap();
    };
    // let $v: $t = ......, .......
    ( @interactive : $interactive:literal, $v:ident : $t:ty, $( $rest:tt )+ ) => {
        $crate::scan!(@interactive: $interactive, $v : $t);
        $crate::scan!(@interactive: $interactive, $( $rest )+);
    };
    // ......
    ( $( $rest:tt )* ) => {
        $crate::scan!(@interactive: false, $( $rest )*);
    };
}

#[macro_export]
macro_rules! scani {
    ( $( $rest:tt )* ) => {
        $crate::scan!(@interactive: true, $( $rest )*);
    };
}
}

mod graph {
    pub trait Direction : Clone {
        fn is_directed() -> bool;
    }
    #[derive(Debug, Clone, std::marker::Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub enum UnDirected {}
    impl Direction for UnDirected {
        fn is_directed() -> bool {
            false
        }
    }
    #[derive(Debug, Clone, std::marker::Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub enum Directed {}
    impl Direction for Directed {
        fn is_directed() -> bool {
            true
        }
    }
    
    
    #[derive(Debug, Clone, std::marker::Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub struct Edge {
        pub to: usize,
        pub weight: i64,
    }
    
    
    pub struct Neighbors<'a> {
        inner: std::slice::Iter<'a, Edge>
    }
    
    impl<'a> Iterator for Neighbors<'a> {
        type Item = &'a usize;
        fn next(&mut self) -> Option<Self::Item> {
            self.inner.next().map(|Edge { to, weight: _ }| to)
        }
    }
    
    pub struct Edges<'a> {
        inner: std::slice::Iter<'a, Edge>
    }
    
    impl<'a> Iterator for Edges<'a> {
        type Item = (&'a usize, &'a i64);
        fn next(&mut self) -> Option<Self::Item> {
            self.inner.next().map(|Edge { to, weight }| (to, weight))
        }
    }
    
    
    pub struct EdgesMut<'a> {
        inner: std::slice::IterMut<'a, Edge>
    }
    
    impl<'a> Iterator for EdgesMut<'a> {
        type Item = (&'a usize, &'a mut i64);
        fn next(&mut self) -> Option<Self::Item> {
            self.inner.next().map(|Edge { to, weight }| (&*to, weight))
        }
    }    
    
    #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
    pub struct InvalidTree;
    impl std::fmt::Display for InvalidTree {
        fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
            write!(f, "Invalid Tree")
        }
    }
    impl std::error::Error for InvalidTree {}
    
    
    pub type DirectedTree = Tree<Directed>;
    pub type UnDirectedTree = Tree<UnDirected>;
    
    #[derive(Debug, Clone)]
    pub struct Tree<D: Direction> {
        size: usize,
        root: usize,
        par: Vec<usize>,
        graph: Vec<Vec<Edge>>,
        _d: std::marker::PhantomData<D>
    }
    
    impl<'a, D: Direction> Tree<D> {
        pub fn from_weighted_edges(edges: Vec<(usize, usize, i64)>) -> Result<Self, InvalidTree> {
            let size = edges.len() + 1;
            let mut par = vec![std::usize::MAX; size];
            let mut graph = vec![vec![]; size];
    
            for (from, to, weight) in edges {
                if from >= size || to >= size || from == to {
                    return Err(InvalidTree);
                }
                if D::is_directed() {
                    if par[to] != std::usize::MAX {
                        return Err(InvalidTree);
                    }
                    par[to] = from;
                }
                graph[from].push(Edge { to, weight });
                if !D::is_directed() {
                    graph[to].push(Edge { to: from, weight });
                }
            }
    
            if !D::is_directed() {
                let mut nt = std::collections::VecDeque::new();
                nt.push_back(0);
                while let Some(now) = nt.pop_front() {
                    for Edge { to, weight: _ } in &graph[now] {
                        if *to != par[now] {
                            if par[*to] != std::usize::MAX {
                                return Err(InvalidTree);
                            }
                            par[*to] = now;
                            nt.push_back(*to);
                        }
                    }
                }
            }
    
            Ok(Tree { size, root: 0, par, graph, _d: std::marker::PhantomData })
        }
    
        #[inline]
        pub fn from_edges(edges: Vec<(usize, usize)>) -> Result<Self, InvalidTree> {
            let edges = edges
                    .into_iter()
                    .map(|(from, to)| (from, to, 1))
                    .collect();
            Self::from_weighted_edges(edges)
        }
    
        /// The parent of root node is std::usize::MAX.
        #[inline]
        pub fn from_par_list(pars: Vec<usize>) -> Result<Self, InvalidTree> {
            let edges = pars
                    .into_iter()
                    .enumerate()
                    .filter(|v| v.1 != std::usize::MAX)
                    .map(|(i, par)| (par, i, 1))
                    .collect();
            Self::from_weighted_edges(edges)
        }
    
        #[inline]
        pub fn neighbors(&'a self, index: usize) -> Neighbors<'a> {
            Neighbors { inner: self.graph[index].iter() }
        }
    
        #[inline]
        pub fn edges(&'a self, index: usize) -> Edges<'a> {
            Edges { inner: self.graph[index].iter() }
        }
    
        #[inline]
        pub fn edges_mut(&'a mut self, index: usize) -> EdgesMut<'a> {
            EdgesMut { inner: self.graph[index].iter_mut() }
        }
    
        #[inline]
        pub fn root(&self) -> usize {
            self.root
        }
    
        #[inline]
        pub fn reroot(&mut self, new: usize) {
            self.root = new;
        }
    
        #[inline]
        pub fn reroot_with_rebuild(&mut self, new: usize) {
            self.reroot(new);
            self.rebuild();
        }
    
        fn rebuild(&mut self) {
            let mut nt = std::collections::VecDeque::new();
            nt.push_back((self.root, std::usize::MAX));
    
            while let Some((now, par)) = nt.pop_front() {
                for Edge { to, weight: _ } in &self.graph[now] {
                    if par != *to {
                        self.par[*to] = now;
                        nt.push_back((*to, now));
                    }
                }
            }
        }
    
        pub fn reroot_with_diameter(&mut self) {
            let mut dist = vec![-1; self.size];
            let mut nt = std::collections::BinaryHeap::new();
            nt.push(std::cmp::Reverse((0, self.root)));
    
            let mut max = (std::i64::MIN, 0);
            while let Some(std::cmp::Reverse((nd, now))) = nt.pop() {
                if dist[now] >= 0 {
                    continue;
                }
                dist[now] = nd;
                max = std::cmp::max(max, (nd, now));
    
                for Edge { to, weight } in &self.graph[now] {
                    if dist[*to] < 0 {
                        nt.push(std::cmp::Reverse((nd + weight, *to)));
                    }
                }
            }
    
            self.reroot_with_rebuild(max.1);
        }
    }

    
    /// If an ancestor earlier than its own rank is searched, std::usize::MAX is returned.  
    pub fn nth_ancestor<D: Direction>(tree: &mut Tree<D>) -> impl Fn(usize, usize) -> usize {
        const MAX_RANK_LOG: usize = 25;
        let mut doubling = vec![vec![std::usize::MAX; tree.size]; MAX_RANK_LOG];
    
        if tree.par[tree.root] != std::usize::MAX {
            tree.rebuild();
        }
    
        for log in 0..MAX_RANK_LOG {
            for now in 0..tree.size {
                if log == 0 {
                    doubling[log][now] = tree.par[now];
                } else {
                    let to = doubling[log-1][now];
                    if to != std::usize::MAX {
                        doubling[log][now] = doubling[log-1][to];
                    }
                }
            }
        }
    
        move |mut now: usize, mut nth: usize| -> usize {
            for log in (0..MAX_RANK_LOG).rev() {
                if nth >= 1 << log {
                    now = doubling[log][now];
                    nth -= 1 << log;
                    if now == std::usize::MAX {
                        break;
                    }
                }
            }
    
            now
        }
    }
    
    
    /// Returns a closure that finds the Lowest Common Ancestor of the two vertices belonging to the tree.
    pub fn lca<D: Direction>(tree: &mut Tree<D>) -> impl Fn(usize, usize) -> usize {
        
        if tree.par[tree.root] != std::usize::MAX {
            tree.rebuild();
        }
        
        let mut max_rank = 0;
        let mut nt = vec![];
        let mut rank = vec![std::u32::MAX; tree.size];
        nt.push((tree.root as u32, 0));
        while let Some((now, r)) = nt.pop() {
            if rank[now as usize] != std::u32::MAX {
                continue;
            }
            rank[now as usize] = r;
            max_rank = std::cmp::max(max_rank, r);
    
            for to in tree.neighbors(now as usize) {
                if *to != tree.par[now as usize] {
                    nt.push((*to as u32, r + 1));
                }
            }
        }

        let max_rank_log = max_rank.next_power_of_two().trailing_zeros() + 1;
        let mut doubling = vec![vec![std::u32::MAX; max_rank_log as usize]; tree.size];
    
        for log in 0..max_rank_log {
            for now in 0..tree.size {
                if log == 0 {
                    doubling[now][log as usize] = tree.par[now] as u32;
                } else {
                    let to = doubling[now][log as usize - 1];
                    if to != std::u32::MAX {
                        doubling[now][log as usize] = doubling[to as usize][log as usize - 1];
                    }
                }
            }
        }
    
        move |mut l: usize, mut r: usize| -> usize {
            if l == r {
                return l;
            }
            if rank[l] > rank[r] {
                std::mem::swap(&mut l, &mut r);
            }
            if rank[r] > rank[l] {
                let mut diff = rank[r] - rank[l];
                let np = diff.next_power_of_two();
                for (log, exp) in (0..=np.trailing_zeros()).rev().scan(np << 1, |s, log| { *s >>= 1; Some((log, *s))}) {
                    if diff >= exp {
                        r = doubling[r][log as usize] as usize;
                        diff -= exp;
                    }
                }
            }
            if l == r {
                return l;
            }
    
            for log in (0..max_rank_log).rev() {
                if doubling[l][log as usize] != doubling[r][log as usize] {
                    l = doubling[l][log as usize] as usize;
                    r = doubling[r][log as usize] as usize;
                }
            }
    
            doubling[l][0] as usize
        }
    }
}