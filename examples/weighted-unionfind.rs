// https://atcoder.jp/contests/abc087/tasks/arc090_b
// use tayu_procon::{
//     scan,
//     unionfind::WeightedUnionFind
// };

// fn main() {
//     scan!(n: usize, m: usize, p: [(usize, usize, i64); m]);

//     let mut uf = WeightedUnionFind::new(n);

//     for (l, r, d) in p {
//         let (l, r) = (l-1, r-1);
//         if let Err(_) = uf.merge(l, r, d) {
//             if uf.diff(l, r) != d {
//                 println!("No");
//                 std::process::exit(0);
//             }
//         }
//     }

//     println!("Yes");
// }

fn main() {
    scan!(n: usize, m: usize, p: [(usize, usize, i64); m]);

    let mut uf = WeightedUnionFind::new(n);

    for (l, r, d) in p {
        let (l, r) = (l - 1, r - 1);
        if let Err(_) = uf.merge(l, r, d) {
            if uf.diff(l, r) != d {
                println!("No");
                std::process::exit(0);
            }
        }
    }

    println!("Yes");
}

use std::cell::RefCell;
use std::collections::VecDeque;
use std::io::{BufRead, Error, Read};
use std::str::SplitWhitespace;
use std::thread_local;

thread_local! {
    static BUF: RefCell<VecDeque<String>> = RefCell::new(VecDeque::new());
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
pub fn scan_string(interactive: bool) -> String {
    BUF_SPLIT_WHITESPACE.with(|buf_str| {
        if let Some(s) = buf_str.borrow_mut().next() {
            return s.to_string();
        }

        refill_buffer(interactive).unwrap();

        if let Some(s) = buf_str.borrow_mut().next() {
            return s.to_string();
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
        { let tmp = $crate::scan_string($interactive).parse::<$t>().unwrap(); tmp }
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
        let $v = $crate::scan_string($interactive).parse::<$t>().unwrap();
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

/////////////////////////////////////////////////////////////////////////////////////////
/// Weighted UnionFind Tree
/////////////////////////////////////////////////////////////////////////////////////////

#[derive(Debug)]
pub struct AlreadySameGroupError(usize, usize);

impl std::fmt::Display for AlreadySameGroupError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "Node {} and Node {} are already belong to the same group.", self.0, self.1) }
}

impl std::error::Error for AlreadySameGroupError {}

/// par[i]    : the parent of node i
/// rank[i]   : the distance of node i from root
/// potential[i] : the potential of the edge between node i and i's parent
pub struct WeightedUnionFind {
    par: Vec<usize>,
    rank: Vec<usize>,
    potential: Vec<i64>,
}

impl WeightedUnionFind {
    pub fn new(size: usize) -> Self {
        Self {
            par: (0..size).collect(),
            rank: vec![0; size],
            potential: vec![0; size],
        }
    }

    pub fn root(&mut self, index: usize) -> usize {
        if self.par[index] == index {
            return index;
        }

        let root = self.root(self.par[index]);
        self.potential[index] += self.potential[self.par[index]];
        self.par[index] = root;
        root
    }

    pub fn is_same(&mut self, l: usize, r: usize) -> bool { self.root(l) == self.root(r) }

    pub fn merge(&mut self, l: usize, r: usize, mut weight: i64) -> Result<(), AlreadySameGroupError> {
        if self.is_same(l, r) {
            return Err(AlreadySameGroupError(l, r));
        }

        weight = weight + self.weight(l) - self.weight(r);

        let (mut l, mut r) = (self.root(l), self.root(r));
        if self.rank[l] < self.rank[r] {
            std::mem::swap(&mut l, &mut r);
            weight = -weight;
        }

        if self.rank[l] == self.rank[r] {
            self.rank[l] += 1;
        }
        self.par[r] = l;

        self.potential[r] = weight;

        Ok(())
    }

    pub fn weight(&mut self, index: usize) -> i64 {
        let _ = self.root(index);
        self.potential[index]
    }

    pub fn diff(&mut self, l: usize, r: usize) -> i64 { self.weight(r) - self.weight(l) }
}
