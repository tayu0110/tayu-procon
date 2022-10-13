// https://judge.yosupo.jp/problem/point_add_range_sum
// use tayu_procon::{
//     scan,
//     segtree::SegmentTree
// };

// fn main() {
//     scan!(n: usize, q: usize, a: [usize; n], p: [(usize, usize, usize); q]);

//     let mut st = SegmentTree::new(n, 0, |l, r| *l + *r);
//     for (i, v) in a.into_iter().enumerate() {
//         st.set(i, v);
//     }

//     for (t, l, r) in p {
//         if t == 0 {
//             st.update_by(l, r, |old, val| *old + *val);
//         } else {
//             println!("{}", st.get(l, r));
//         }
//     }
// }

fn main() {
    scan!(n: usize, q: usize, a: [usize; n], p: [(usize, usize, usize); q]);

    let mut st = SegmentTree::new(n, 0, |l, r| *l + *r);
    for (i, v) in a.into_iter().enumerate() {
        st.set(i, v);
    }

    for (t, l, r) in p {
        if t == 0 {
            st.update_by(l, r, |old, val| *old + *val);
        } else {
            println!("{}", st.get(l, r));
        }
    }
}

use std::cell::RefCell;
use std::collections::VecDeque;
use std::io::{
    Read, BufRead, Error
};
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

pub struct SegmentTree<M>
where M: Clone {
    size: usize,
    e: M,
    op: fn(&M, &M) -> M,
    tree: Vec<M>
}

impl<M> SegmentTree<M>
where M: Clone {
    pub fn new(size: usize, e: M, op: fn(&M, &M) -> M) -> Self {
        let tree = vec![e.clone(); size << 1];
        Self { size, e, op, tree }
    }

    pub fn set(&mut self, index: usize, val: M) {
        self.update_by(index, val, |_, act| act.clone());
    }

    pub fn update_by(&mut self, mut index: usize, val: M, f: fn(old: &M, act: &M) -> M) {
        index += self.size;
        self.tree[index] = f(&self.tree[index], &val);
        while index >> 1 > 0 {
            index >>= 1;
            self.tree[index] = self.op(&self.tree[index<<1], &self.tree[index<<1|1]);
        }
    }
    
    pub fn get(&self, left: usize, right: usize) -> M {
        if left >= right {
            return self.e.clone();
        }

        let (mut l, mut r) = (left + self.size, right + self.size);
        let (mut res_l, mut res_r) = (self.e.clone(), self.e.clone());
        while l < r {
            if l & 1 != 0 {
                res_l = self.op(&self.tree[l], &res_l);
                l += 1;
            }
            if r & 1 != 0 {
                r -= 1;
                res_r = self.op(&res_r, &self.tree[r]);
            }
            l >>= 1;
            r >>= 1;
        }

        self.op(&res_l, &res_r)
    }

    fn op(&self, lhs: &M, rhs: &M) -> M { let op = self.op; op(&lhs, &rhs) }
}
