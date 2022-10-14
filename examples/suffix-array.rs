// https://judge.yosupo.jp/problem/suffixarray
// use tayu_procon::{
//     scan,
//     utility::SuffixArray
// };

// fn main() {
//     scan!(s: String);

//     let sa = SuffixArray::new(s);

//     let sa = sa.get_sa();

//     for (i, sa) in sa.into_iter().enumerate() {
//         if i > 0 {
//             print!(" ");
//         }
//         print!("{}", sa);
//     }
//     println!("");
// }

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(s: String);

    let sa = SuffixArray::new(s);

    for (i, sa) in sa.get_sa().into_iter().enumerate() {
        if i > 0 {
            write!(out, " {}", sa).ok();
        } else {
            write!(out, "{}", sa).ok();
        }
    }
    writeln!(out, "").ok();
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

////////////////////////////////////////////////////////////////////////////////
// Suffix Array
////////////////////////////////////////////////////////////////////////////////

// s[i] := A suffix of the string 's' that begins from i-th element. (0 <= i < s.len()-1)
//      S   : s[i] < s[i+1]
//      L   : s[i] > s[i+1]
//      LMS : s[i-1] = L-type && s[i] = S-type (Left-Most-S)
#[derive(Debug, Clone, Copy, PartialEq)]
#[repr(u8)]
enum Type {
    S, L, LMS
}

pub struct SuffixArray {
    s: Vec<u32>,
    sa: Vec<usize>
}

impl SuffixArray {
    const CHARS: usize = 1 << 8;

    pub fn new(s: impl Into<String>) -> Self {
        let s = [s.into().bytes().map(|b| b as u32).collect(), vec![0]].concat();
        let mut sa = vec![std::usize::MAX; s.len()];
        Self::sa_is(Self::CHARS, &s, &mut sa);

        Self { s, sa }
    }

    fn sa_is(kinds: usize, s: &[u32], sa: &mut Vec<usize>) {
        let mut types = vec![Type::S; s.len()];
        let mut lms_indices = vec![vec![]; kinds];
        let mut char_num = vec![0u32; kinds];

        for (i, c) in s.iter().enumerate().rev() {
            char_num[*c as usize] += 1;

            if i == s.len() - 1 {
                continue;
            }
            
            let nc = &s[i+1];
            types[i] = if c < nc {
                Type::S
            } else if c > nc {
                if types[i+1] == Type::S {
                    types[i+1] = Type::LMS;
                    lms_indices[*nc as usize].push(i as u32 + 1);
                }
                Type::L
            } else {
                // if s[i+1] := x, and s[i] := ax := a{s[i+1]}
                // if c != nc, then x[0] == a. so, s[i+1] := x := a{s[i+2]}
                // so s[i] <> s[i+1] == a{s[i+1]} <> a{s[i+2]}
                //      if s[i+1] < s[i+2] (types[i+1] = S), then s[i] < s[i+1] and types[i] = S
                //      otherwise s[i+1] > s[i+2] (types[i+1] = L), then s[i] > s[i+1] and types[i] = L
                types[i+1]
            }
        }

        let char_start = [vec![0], char_num.iter().scan(0, |s, n| { *s += *n; Some(*s) }).collect()].concat();

        // Calculate Pseudo SA
        Self::induced_sort(&lms_indices.into_iter().flatten().collect::<Vec<_>>(), &char_start, &char_num, s, &types, sa);

        let mut rank = 0;
        let mut lms_prev = (std::usize::MAX, std::usize::MAX);
        let mut lms_perm = vec![];
        let mut lms_indices = vec![std::u32::MAX; s.len()];
        for index in sa.iter().take(s.len()).filter(|index| types[**index] == Type::LMS) {
            if lms_prev == (std::usize::MAX, std::usize::MAX) {
                lms_prev = (*index, *index);
                lms_indices[*index] = rank;
                lms_perm.push(*index as u32);
            } else {
                let (l, mut r) = (*index, *index + 1);
                while r < types.len() && types[r] != Type::LMS {
                    r += 1;
                }
                    
                let (pl, pr) = lms_prev;
                if pr - pl != r - l || s[pl..pr+1] != s[l..r+1] {
                    rank += 1;
                    lms_prev = (l, r);
                }
                lms_indices[l] = rank;
                lms_perm.push(l as u32);
            }
        }

        let lms_indices = if lms_perm.len() as u32 == rank + 1 {
            lms_perm
        } else {
            let (restore_index, lms_ranks) = lms_indices
                    .into_iter()
                    .enumerate()
                    .filter(|(_, c)| *c != std::u32::MAX)
                    .map(|(i, c)| (i as u32, c))
                    .unzip::<u32, u32, Vec<u32>, Vec<u32>>();
            Self::sa_is(rank as usize + 1, &lms_ranks, sa);
            sa.into_iter()
                .take(lms_ranks.len())
                .map(|i| restore_index[*i])
                .collect()
        };

        Self::induced_sort(&lms_indices, &char_start, &char_num, s, &types, sa);
    }

    fn induced_sort(lms_indices: &[u32], char_start: &[u32], char_num: &[u32], s: &[u32], types: &[Type], sa: &mut Vec<usize>) {
        let kinds = char_start.len();
        sa.iter_mut().take(s.len()).for_each(|sa| *sa = std::usize::MAX);
        sa[0] = s.len() - 1;

        let mut checked = 1;
        let mut filled = vec![0; kinds];
        for (i, lms) in lms_indices.into_iter().enumerate() {
            let c = s[*lms as usize];

            if i > 0 && c != s[lms_indices[i-1] as usize] {
                let target = char_start[c as usize] + char_num[c as usize] - 1;

                while checked <= target {
                    if sa[checked as usize] != std::usize::MAX && sa[checked as usize] > 0 && types[sa[checked as usize]-1] == Type::L {
                        let nc = s[sa[checked as usize]-1];
                        sa[(char_start[nc as usize] + filled[nc as usize]) as usize] = sa[checked as usize] - 1;
                        filled[nc as usize] += 1;
                    }

                    checked += 1;
                }
            }

            if types[*lms as usize - 1] == Type::L {
                let nc = s[*lms as usize - 1];
                sa[(char_start[nc as usize] + filled[nc as usize]) as usize] = *lms as usize - 1;
                filled[nc as usize] += 1;
            }
        }

        for i in checked as usize..s.len() {
            if sa[i] != std::usize::MAX && sa[i] > 0 && types[sa[i]-1] == Type::L {
                let c = s[sa[i]-1];
                sa[(char_start[c as usize] + filled[c as usize]) as usize] = sa[i] - 1;
                filled[c as usize] += 1;
            }
        }

        let mut filled = vec![0; kinds];
        for i in (0..s.len()).rev() {
            if sa[i] != std::usize::MAX && sa[i] > 0 && types[sa[i]-1] != Type::L {
                let c = s[sa[i]-1];
                sa[(char_start[c as usize] + char_num[c as usize] - 1 - filled[c as usize]) as usize] = sa[i] - 1;
                filled[c as usize] += 1;
            }
        }
    }

    pub fn get_sa(&self) -> &[usize] {
        &self.sa[1..]
    }

    /// LCPA\[i\] := Longest Common Prefix between s\[sa\[i\]\] and s\[sa\[i+1\]\]
    pub fn lcp_array(&self) -> Vec<usize> {
        let mut rank = vec![0; self.sa.len()-1];
        for (i, sa) in self.sa.iter().enumerate().skip(1) {
            rank[*sa] = i;
        }

        let mut lcp = 0;
        let mut lcpa = vec![0; self.sa.len()-2];
        for index in rank {
            if index == self.sa.len() - 1 {
                lcp = 0;
                continue;
            }
        
            let (pos_l, pos_r) = (self.sa[index], self.sa[index+1]);
            while self.s[lcp + pos_l] == self.s[lcp + pos_r] {
                lcp += 1;
            }
            lcpa[index-1] = lcp;

            lcp = lcp.saturating_sub(1);
        }
        lcpa
    }
}
