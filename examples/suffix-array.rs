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
pub struct SuffixArray {
    s: Vec<u32>,
    sa: Vec<u32>
}

impl SuffixArray {
    // s[i] := A suffix of the string 's' that begins from i-th element. (0 <= i < s.len()-1)
    //      S   : s[i] < s[i+1]
    //      L   : s[i] > s[i+1]
    //      LMS : s[i-1] = L-type && s[i] = S-type (Left-Most-S)
    const S_TYPE: u8 = 0;
    const L_TYPE: u8 = 1;
    const CHARS: usize = 1 << 8;
    const THRESHOLD_NAIVE: usize = 10;
    const TYPE_DECODE_MASK: [u8; 8] = [1, 2, 4, 8, 16, 32, 64, 128];

    pub fn new(s: impl Into<String>) -> Self {
        let s = s.into().bytes().map(|b| b as u32).chain(vec![0].into_iter()).collect::<Vec<_>>();
        let mut sa = vec![std::u32::MAX; s.len()];
        Self::sa_is(Self::CHARS, &s, &mut sa, &mut vec![]);

        Self { s, sa }
    }

    #[inline]
    fn sa_naive(s: &[u32], sa: &mut [u32]) {
        sa.iter_mut().take(s.len()).enumerate().for_each(|(i, v)| *v = i as u32);
        sa[0..s.len()].sort_by_key(|i| &s[*i as usize..]);
    }

    #[inline(always)]
    const fn decode_type(index: usize, types: &[u8]) -> u8 {
        let mask = index & 0b111;
        (types[index >> 3] & Self::TYPE_DECODE_MASK[mask]) >> mask
    }

    #[inline(always)]
    fn write_type(index: usize, ls: u8, types: &mut [u8]) {
        if ls == Self::S_TYPE {
            types[index >> 3] |= ls << (index & 0b111);
        } else {
            types[index >> 3] ^= ls << (index & 0b111);
        }
    }

    #[inline(always)]
    const fn is_lms(index: usize, types: &[u8]) -> bool {
        index > 0 && Self::decode_type(index, &types) == Self::S_TYPE && Self::decode_type(index-1, &types) == Self::L_TYPE
    }

    fn sa_is(kinds: usize, s: &[u32], sa: &mut [u32], lms_next: &mut Vec<u32>) {
        if s.len() <= Self::THRESHOLD_NAIVE {
            Self::sa_naive(s, sa);
            return;
        }

        let mut lms_prev = std::u32::MAX;
        if lms_next.len() < s.len() {
            *lms_next = vec![std::u32::MAX; s.len()];
        }
        let mut types = vec![0u8; (s.len() + 7) >> 3];
        let mut lms_indices = vec![];
        let mut char_start = vec![0u32; kinds+1];

        for (i, c) in s.iter().enumerate().rev() {
            char_start[*c as usize + 1] += 1;
            lms_next[i] = std::u32::MAX;

            if i == s.len() - 1 {
                continue;
            }
            
            let nc = &s[i+1];
            let t = if c < nc {
                Self::S_TYPE
            } else if c > nc {
                if Self::decode_type(i+1, &types) == Self::S_TYPE {
                    lms_indices.push(i as u32 + 1);
                    lms_next[i+1] = lms_prev;
                    lms_prev = i as u32 + 1;
                }
                Self::L_TYPE
            } else {
                Self::decode_type(i+1, &types)
            };
            Self::write_type(i, t, &mut types);
        }

        for i in 0..kinds {
            char_start[i+1] += char_start[i];
        }

        // Calculate Pseudo SA
        let max_lms_num = Self::induced_sort(&lms_indices, &char_start, s, &types, sa);

        // If there is only one LMS-Type and the type[0] one is not S-Type, there is no need for a second sort
        // since the order of operations of the sort is unique since all elements except the last element are L-Types.
        if lms_indices.len() == 1 && Self::decode_type(0, &types) != Self::S_TYPE {
            return;
        }
        // If there is only one LMS-Type for each bucket per character type, then a second sort is not necessary
        // because the order of the sorting operations is unique.
        if max_lms_num == 1 {
            return;
        }

        let mut rank = 0;
        let mut lms_prev = (std::usize::MAX, std::usize::MAX);
        let lms_ranks = lms_next;
        for (i, index) in sa.iter().take(s.len()).filter(|index| Self::is_lms(**index as usize, &types)).enumerate() {
            lms_indices[i] = *index;
            let (l, r) = (*index as usize, lms_ranks[*index as usize] as usize);
            let (pl, pr) = lms_prev;
            if pr - pl != r - l || s[pl..pr+1] != s[l..r+1] {
                rank += 1;
                lms_prev = (l, r);
            }
            lms_ranks[*index as usize] = rank - 1;
        }

        if lms_indices.len() as u32 != rank + 1 {
            let (restore_index, new_s) = lms_ranks
                    .iter()
                    .take(s.len())
                    .enumerate()
                    .filter(|(_, c)| c != &&std::u32::MAX)
                    .map(|(i, c)| (i as u32, *c))
                    .unzip::<u32, u32, Vec<u32>, Vec<u32>>();
            Self::sa_is(rank as usize + 1, &new_s, sa, lms_ranks);
            lms_indices
                .iter_mut()
                .zip(sa.into_iter())
                .for_each(|(lms, i)| *lms = restore_index[*i as usize]);
        };

        Self::induced_sort(&lms_indices, &char_start, s, &types, sa);
    }

    #[inline]
    fn induced_sort(lms_indices: &[u32], char_start: &[u32], s: &[u32], types: &[u8], sa: &mut [u32]) -> u32 {    
        let kinds = char_start.len() - 1;
        sa[0] = s.len() as u32 - 1;

        let mut filled_lms = vec![0; kinds];
        for (lms, c) in lms_indices.into_iter().map(|lms| (*lms, s[*lms as usize] as usize)) {
            sa[(char_start[c+1] - 1 - filled_lms[c]) as usize] = lms;
            filled_lms[c] += 1;
        }

        let mut max_lms_num = 0;
        let mut filled = vec![0; kinds];
        for backet_index in 0..kinds {
            let mut rem = filled[backet_index];
            let mut checked = char_start[backet_index] as usize;
            while rem > 0 {
                if sa[checked] > 0 && Self::decode_type(sa[checked] as usize - 1, &types) == Self::L_TYPE {
                    let nc = s[sa[checked] as usize - 1] as usize;
                    sa[(char_start[nc]  + filled[nc]) as usize] = sa[checked] - 1;
                    filled[nc] += 1;
                    if backet_index == nc {
                        rem += 1;
                    }
                }
                checked += 1;
                rem -= 1;
            }

            for lms_index in 0..filled_lms[backet_index] {
                let lms = sa[(char_start[backet_index+1] - 1 - lms_index) as usize] as usize;
                if lms > 0 && Self::decode_type(lms - 1, &types) == Self::L_TYPE {
                    let nc = s[lms - 1] as usize;
                    sa[(char_start[nc] + filled[nc]) as usize] = lms as u32 - 1;
                    filled[nc] += 1;
                }
                if backet_index != 0 {
                    sa[(char_start[backet_index+1] - 1 - lms_index) as usize] = std::u32::MAX;
                }
            }

            max_lms_num = std::cmp::max(max_lms_num, filled_lms[backet_index]);
            filled[backet_index] = 0;
        }

        // If there is only one LMS-Type and the type[0] one is not S-Type, there is no need for a second sort
        // since the order of operations of the sort is unique since all elements except the last element are L-Types.
        if lms_indices.len() == 1 && Self::decode_type(0, &types) != Self::S_TYPE {
            return max_lms_num;
        }

        for i in (0..s.len()).rev() {
            if sa[i] != std::u32::MAX && sa[i] > 0 && Self::decode_type(sa[i] as usize - 1, &types) != Self::L_TYPE {
                let c = s[sa[i] as usize - 1];
                sa[(char_start[c as usize + 1] - 1 - filled[c as usize]) as usize] = sa[i] - 1;
                filled[c as usize] += 1;
            }
        }

        max_lms_num
    }

    #[inline]
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