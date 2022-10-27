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
    sa: Vec<u32>
}

impl SuffixArray {
    const CHARS: usize = 1 << 8;
    const THRESHOLD_NAIVE: usize = 10;

    pub fn new(s: impl Into<String>) -> Self {
        let s = s.into().bytes().map(|b| b as u32).chain(vec![0].into_iter()).collect::<Vec<_>>();
        let mut sa = vec![std::u32::MAX; s.len()];
        Self::sa_is(Self::CHARS, &s, &mut sa);

        Self { s, sa }
    }

    #[inline]
    fn sa_naive(s: &[u32], sa: &mut [u32]) {
        sa.iter_mut().take(s.len()).enumerate().for_each(|(i, v)| *v = i as u32);
        sa[0..s.len()].sort_by_key(|i| &s[*i as usize..]);
    }

    fn sa_is(kinds: usize, s: &[u32], sa: &mut [u32]) {
        if s.len() <= Self::THRESHOLD_NAIVE {
            Self::sa_naive(s, sa);
            return;
        }

        let mut lms_prev = std::u32::MAX;
        let mut lms_next = vec![std::u32::MAX; s.len()];
        let mut types = vec![Type::S; s.len()];
        // let mut lms_indices = vec![vec![]; kinds];
        let mut lms_indices = vec![];
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
                    // lms_indices[*nc as usize].push(i as u32 + 1);
                    lms_indices.push(i as u32 + 1);
                    lms_next[i+1] = lms_prev;
                    lms_prev = i as u32 + 1;
                }
                Type::L
            } else {
                types[i+1]
            };
        }

        let char_start = vec![0].into_iter().chain(char_num.iter().scan(0, |s, n| { *s += n; Some(*s) })).collect::<Vec<_>>();

        // Calculate Pseudo SA
        // Self::induced_sort(&lms_indices.into_iter().flatten().collect::<Vec<_>>(), &char_start, &char_num, s, &types, sa);
        let max_lms_num = Self::induced_sort(&lms_indices, &char_start, &char_num, s, &types, sa);

        // If there is only one LMS-Type and the type[0] one is not S-Type, there is no need for a second sort
        // since the order of operations of the sort is unique since all elements except the last element are L-Types.
        if lms_indices.len() == 1 && types[0] != Type::S {
            return;
        }
        // If there is only one LMS-Type for each bucket per character type, then a second sort is not necessary
        // because the order of the sorting operations is unique.
        if max_lms_num == 1 {
            return;
        }

        let mut rank = 0;
        let mut lms_prev = (std::usize::MAX, std::usize::MAX);
        let mut lms_sorted = vec![];
        Vec::reserve_exact(&mut lms_sorted, lms_indices.len());
        let mut lms_ranks = lms_next;
        for index in sa.iter().take(s.len()).filter(|index| types[**index as usize] == Type::LMS) {
            if lms_prev == (std::usize::MAX, std::usize::MAX) {
                lms_prev = (*index as usize, *index as usize);
                lms_ranks[*index as usize] = rank;
                lms_sorted.push(*index);
            } else {
                let (l, r) = (*index as usize, lms_ranks[*index as usize] as usize);
                let (pl, pr) = lms_prev;
                if pr - pl != r - l || s[pl..pr+1] != s[l..r+1] {
                    rank += 1;
                    lms_prev = (l, r);
                }
                lms_ranks[l] = rank;
                lms_sorted.push(l as u32);
            }
        }

        let lms_indices = if lms_sorted.len() as u32 == rank + 1 {
            lms_sorted
        } else {
            let (restore_index, new_s) = lms_ranks
                    .into_iter()
                    .enumerate()
                    .filter(|(_, c)| *c != std::u32::MAX)
                    .map(|(i, c)| (i as u32, c))
                    .unzip::<u32, u32, Vec<u32>, Vec<u32>>();
            Self::sa_is(rank as usize + 1, &new_s, sa);
            sa.into_iter()
                .take(new_s.len())
                .map(|i| restore_index[*i as usize])
                .collect()
        };

        Self::induced_sort(&lms_indices, &char_start, &char_num, s, &types, sa);
    }

    #[inline]
    fn induced_sort(lms_indices: &[u32], char_start: &[u32], char_num: &[u32], s: &[u32], types: &[Type], sa: &mut [u32]) -> u32 {
        let kinds = char_start.len();
        sa[0] = s.len() as u32 - 1;

        let mut filled_lms = vec![0; kinds];
        for (lms, c) in lms_indices.into_iter().map(|lms| (*lms, s[*lms as usize] as usize)) {
            sa[(char_start[c] + char_num[c] - 1 - filled_lms[c]) as usize] = lms;
            filled_lms[c] += 1;
        }

        let mut max_lms_num = 0;
        let mut backet_index = 0;
        let mut filled = vec![0; kinds];
        while backet_index < kinds {
            let mut rem = filled[backet_index];
            let mut checked = char_start[backet_index] as usize;
            while rem > 0 {
                if sa[checked] > 0 && types[sa[checked] as usize - 1] == Type::L {
                    let nc = s[sa[checked] as usize - 1] as usize;
                    sa[char_start[nc] as usize + filled[nc] as usize] = sa[checked] - 1;
                    filled[nc] += 1;
                    if backet_index == nc {
                        rem += 1;
                    }
                }
                checked += 1;
                rem -= 1;
            }

            for lms_index in 0..filled_lms[backet_index] {
                let lms = sa[(char_start[backet_index] + char_num[backet_index] - 1 - lms_index) as usize] as usize;
                if lms > 0 && types[lms - 1] == Type::L {
                    let nc = s[lms - 1] as usize;
                    sa[char_start[nc] as usize + filled[nc] as usize] = lms as u32 - 1;
                    filled[nc] += 1;
                }
                if backet_index != 0 {
                    sa[(char_start[backet_index] + char_num[backet_index] - 1 - lms_index) as usize] = std::u32::MAX;
                }
            }

            max_lms_num = std::cmp::max(max_lms_num, filled_lms[backet_index]);
            filled[backet_index] = 0;
            backet_index += 1;
        }

        if lms_indices.len() == 1 && types[0] != Type::S {
            return max_lms_num;
        }

        // let mut backet_index = 1;
        // let mut checked = 1;
        // let mut filled = vec![0; kinds];
        // for (i, lms) in lms_indices.into_iter().enumerate() {
        //     let c = s[*lms as usize] as usize;

        //     if i > 0 && c != s[lms_indices[i-1] as usize] as usize {
        //         let target = char_start[c] as usize + char_num[c] as usize - 1;

        //         while checked < target {
        //             let mut rem = filled[backet_index];
        //             while rem > 0 {
        //                 if sa[checked] != std::u32::MAX && sa[checked] > 0 && types[sa[checked] as usize - 1] == Type::L {
        //                     let nc = s[sa[checked] as usize - 1] as usize;
        //                     sa[(char_start[nc] + filled[nc]) as usize] = sa[checked] - 1;
        //                     filled[nc] += 1;
        //                     if nc == backet_index {
        //                         rem += 1;
        //                     }
        //                 }
        //                 rem -= 1;
        //                 checked += 1;
        //             }

        //             checked = char_start[backet_index] as usize + char_num[backet_index] as usize;
        //             filled[backet_index] = 0;
        //             backet_index += 1;
        //         }
        //     }

        //     if types[*lms as usize - 1] == Type::L {
        //         let nc = s[*lms as usize - 1] as usize;
        //         sa[(char_start[nc] + filled[nc]) as usize] = *lms - 1;
        //         filled[nc] += 1;
        //     }
        // }

        // while checked < s.len() {
        //     let mut rem = filled[backet_index];
        //     while rem > 0 {
        //         if sa[checked] != std::u32::MAX && sa[checked] > 0 && types[sa[checked] as usize - 1] == Type::L {
        //             let nc = s[sa[checked] as usize - 1] as usize;
        //             sa[(char_start[nc] + filled[nc]) as usize] = sa[checked] - 1;
        //             filled[nc] += 1;
        //             if nc == backet_index {
        //                 rem += 1;
        //             }
        //         }
                
        //         rem -= 1;
        //         checked += 1;
        //     }

        //     checked = char_start[backet_index] as usize + char_num[backet_index] as usize;
        //     filled[backet_index] = 0;
        //     backet_index += 1;
        // }

        for i in (0..s.len()).rev() {
            if sa[i] != std::u32::MAX && sa[i] > 0 && types[sa[i] as usize - 1] != Type::L {
                let c = s[sa[i] as usize - 1];
                sa[(char_start[c as usize] + char_num[c as usize] - 1 - filled[c as usize]) as usize] = sa[i] - 1;
                filled[c as usize] += 1;
            }
        }

        max_lms_num
    }

    pub fn get_sa(&self) -> &[u32] {
        &self.sa[1..]
    }

    /// LCPA\[i\] := Longest Common Prefix between s\[sa\[i\]\] and s\[sa\[i+1\]\]
    pub fn lcp_array(&self) -> Vec<usize> {
        let mut rank = vec![0; self.sa.len()-1];
        for (i, sa) in self.sa.iter().enumerate().skip(1) {
            rank[*sa as usize] = i;
        }

        let mut lcp = 0;
        let mut lcpa = vec![0; self.sa.len()-2];
        for index in rank {
            if index == self.sa.len() - 1 {
                lcp = 0;
                continue;
            }
        
            let (pos_l, pos_r) = (self.sa[index], self.sa[index+1]);
            while self.s[lcp + pos_l as usize] == self.s[lcp + pos_r as usize] {
                lcp += 1;
            }
            lcpa[index-1] = lcp;

            lcp = lcp.saturating_sub(1);
        }
        lcpa
    }
}