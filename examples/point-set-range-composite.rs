// https://judge.yosupo.jp/submission/108278
mod iolib {
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

pub struct SegmentTree<M>
where M: Clone {
    size: usize,
    e: M,
    op: fn(&M, &M) -> M,
    tree: Vec<M>
}

impl<M> SegmentTree<M>
where M: Clone {
    /// * `size` - Number of elements in the data array to be managed
    /// * `e`    - Identity element of the monoid that the data represents
    /// * `op`   - Operation applied to data (If the operation is to fold the data toward the right, op(a, b) must return b*a as the result)
    #[inline]
    pub fn new(size: usize, e: M, op: fn(&M, &M) -> M) -> Self {
        let tree = vec![e.clone(); size << 1];
        Self { size, e, op, tree }
    }

    /// * `vec`  - Initial state of the data array to be managed
    /// * `e`    - Identity element of the monoid that the data represents
    /// * `op`   - Operation applied to data (If the operation is to fold the data toward the right, op(a, b) must return b*a as the result)
    pub fn from_vec(vec: &Vec<M>, e: M, op: fn(&M, &M) -> M) -> Self {
        let size = vec.len();
        let mut tree = [vec![e.clone(); size], vec.clone()].concat();

        for i in (0..(size<<1)-1).rev().step_by(2).take_while(|i| i>>1 > 0) {
            tree[i>>1] = op(&tree[i], &tree[i|1]);
        }

        Self { size, e, op, tree }
    }

    #[inline]
    pub fn set(&mut self, index: usize, val: M) {
        self.update_by(index, val, |_, act| act.clone());
    }

    pub fn update_by(&mut self, mut index: usize, val: M, f: fn(old: &M, act: &M) -> M) {
        index += self.size;
        self.tree[index] = f(&self.tree[index], &val);
        while index >> 1 > 0 {
            index >>= 1;
            self.tree[index] = self.op(&self.tree[index<<1], &self.tree[index<<1|1], false);
        }
    }

    fn fold(&self, left: usize, right: usize, fold_right: bool) -> M {
        if left >= right {
            return self.e.clone();
        }

        let (mut l, mut r) = (left + self.size, right + self.size);
        let (mut res_l, mut res_r) = (self.e.clone(), self.e.clone());
        while l < r {
            if l & 1 != 0 {
                res_l = self.op(&self.tree[l], &res_l, fold_right);
                l += 1;
            }
            if r & 1 != 0 {
                res_r = self.op(&res_r, &self.tree[r-1], fold_right);
            }
            l >>= 1;
            r >>= 1;
        }

        self.op(&res_l, &res_r, false)
    }
    
    /// Fold the operation in a leftward direction.
    /// That is, you obtain op(t_{l}, op(t_{l+1}, op(t_{l+2}, ...op(t_{r-2}, t_{r-1})...))) as a result.
    #[inline]
    pub fn foldl(&self, left: usize, right: usize) -> M {
        self.fold(left, right, false)
    }

    /// Fold the operation in a rightward direction.
    /// That is, you obtain op(op(op(...op(t_{l}, t_{l+1}), t_{l+2}), ..., t_{r-2}), t_{r_1}) as a result.
    #[inline]
    pub fn foldr(&self, left: usize, right: usize) -> M {
        self.fold(left, right, true)
    }

    #[inline]
    fn op(&self, lhs: &M, rhs: &M, fold_right: bool) -> M { if !fold_right { (self.op)(&lhs, &rhs) } else { (self.op)(&rhs, &lhs) } }
}

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    const MOD: usize = 998244353;
    scan!(n: usize, q: usize, p: [(usize, usize); n], q: [(usize, usize, usize, usize); q]);

    let mut st = SegmentTree::from_vec(&p, (1, 0), |&(a1, b1), &(a2, b2)| (a1*a2 % MOD, (a2*b1+b2) % MOD));

    for (t, l, r, x) in q {
        if t == 0 {
            st.set(l, (r, x));
        } else {
            let (a, b) = st.foldr(l, r);
            // println!("{}", (a * x + b) % MOD);
            writeln!(out, "{}", (a * x + b) % MOD).ok();
        }
    }
}