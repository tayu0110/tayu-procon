////////////////////////////////////////////////////////////////////////////////
// Vec utility
////////////////////////////////////////////////////////////////////////////////

pub trait BinarySearch<T> {
    type Output;
    fn lower_bound(&self, _target: T) -> Option<Self::Output> { unimplemented!() }
    fn upper_bound(&self, _target: T) -> Option<Self::Output> { unimplemented!() }
    /// Return the following 'l'. (If need the following 'r', use upper_bound_by().)  
    ///     L <------  f()=true  ------> lr <------  f()=false  ------> R
    fn lower_bound_by(&self, _f: impl Fn(&T) -> bool) -> Option<Self::Output> { unimplemented!() }
    /// Return the following 'r'. (If need the following 'l', use lower_bound_by().)  
    ///     L <------  f()=true  ------> lr <------  f()=false  ------> R
    fn upper_bound_by(&self, _f: impl Fn(&T) -> bool) -> Option<Self::Output> { unimplemented!() }
}

impl<T: Clone + PartialEq + PartialOrd> BinarySearch<T> for &[T] {
    type Output = usize;
    fn lower_bound(&self, target: T) -> Option<Self::Output> {
        let (mut l, mut r) = (-1i32, self.len() as i32);
        while r - l > 1 {
            let m = (r + l) / 2;
            if self[m as usize] < target {
                l = m;
            } else {
                r = m;
            }
        }
        if r == self.len() as i32 {
            None
        } else {
            Some(r as usize)
        }
    }
    fn upper_bound(&self, target: T) -> Option<Self::Output> {
        let (mut l, mut r) = (-1i32, self.len() as i32);
        while r - l > 1 {
            let m = (r + l) / 2;
            if self[m as usize] <= target {
                l = m;
            } else {
                r = m;
            }
        }
        if r == self.len() as i32 {
            None
        } else {
            Some(r as usize)
        }
    }
    fn lower_bound_by(&self, f: impl Fn(&T) -> bool) -> Option<Self::Output> {
        let (mut l, mut r) = (-1i32, self.len() as i32);
        while r - l > 1 {
            let m = (r + l) / 2;
            if f(&self[m as usize]) {
                l = m;
            } else {
                r = m;
            }
        }
        if l == -1 {
            None
        } else {
            Some(l as usize)
        }
    }
    fn upper_bound_by(&self, f: impl Fn(&T) -> bool) -> Option<Self::Output> {
        let (mut l, mut r) = (-1i32, self.len() as i32);
        while r - l > 1 {
            let m = (r + l) / 2;
            if f(&self[m as usize]) {
                l = m;
            } else {
                r = m;
            }
        }
        if r == self.len() as i32 {
            None
        } else {
            Some(r as usize)
        }
    }
}

impl<T: Clone + PartialEq + PartialOrd> BinarySearch<T> for Vec<T> {
    type Output = usize;
    fn lower_bound(&self, target: T) -> Option<Self::Output> {
        self.as_slice().lower_bound(target)
    }
    fn upper_bound(&self, target: T) -> Option<Self::Output> {
        self.as_slice().upper_bound(target)
    }
    fn lower_bound_by(&self, f: impl Fn(&T) -> bool) -> Option<Self::Output> {
        self.as_slice().lower_bound_by(f)
    }
    fn upper_bound_by(&self, f: impl Fn(&T) -> bool) -> Option<Self::Output> {
        self.as_slice().upper_bound_by(f)
    }
}




////////////////////////////////////////////////////////////////////////////////
// String Utility
////////////////////////////////////////////////////////////////////////////////

pub trait IntoVec<T> {
    fn into_vec(&self) -> Vec<T>;
}

impl IntoVec<char> for String {
    fn into_vec(&self) -> Vec<char> {
        self.chars().collect()
    }
}

impl IntoVec<u8> for String {
    fn into_vec(&self) -> Vec<u8> {
        self.bytes().collect()
    }
}

macro_rules! into_vec_impl {
    ( $t:ty , $( $rest:tt )+ ) => {
        into_vec_impl!($t);
        into_vec_impl!($( $rest )+);
    };
    ( $t:ty ) => {
        impl IntoVec<$t> for String {
            fn into_vec(&self) -> Vec<$t> {
                self.bytes().map(|v| v as $t).collect()
            }
        }
    };
}

into_vec_impl!(u16, u32, u64, u128, usize, i16, i32, i64, i128, isize);

pub trait SubString {
    fn substring(&self, start: usize, len: usize) -> String;
}

impl SubString for String {
    fn substring(&self, start: usize, len: usize) -> String {
        let end = std::cmp::min(self.len(), start + len);

        self[start..end].to_string()
    }
}

impl SubString for &str {
    fn substring(&self, start: usize, len: usize) -> String {
        let end = std::cmp::min(self.len(), start + len);

        self[start..end].to_string()
    }
}

/// For given string S, return an array that records as the i-th element the longest common prefix of S and the substring starting from the i-th element of S.
// https://atcoder.jp/contests/abc135/submissions/34695512
pub fn zalgorithm(s: impl Into<String>) -> Vec<usize> {
    let s: String = s.into();
    let mut z = vec![0; s.len()];
    z[0] = s.len();

    let (mut i, mut j) = (1, 0);
    while i < s.len() {
        while i + j < s.len() && &s[j..j+1] == &s[i+j..i+j+1] {
            j += 1;
        }
        z[i] = j;

        if j == 0 {
            i += 1;
            continue;
        }

        let mut k = 1;
        while i + k < s.len() && k + z[k] < j {
            z[i+k] = z[k];
            k += 1;
        }

        i += k;
        j -= k;
    }

    z
}


////////////////////////////////////////////////////////////////////////////////
// Suffix Array
////////////////////////////////////////////////////////////////////////////////

// s[i] := A suffix of the string 's' that begins from i-th element. (0 <= i < s.len()-1)
//      S   : s[i] < s[i+1]
//      L   : s[i] > s[i+1]
//      LMS : s[i-1] = L-type && s[i] = S-type (Left-Most-S)
#[derive(Debug, Clone, Copy, PartialEq)]
enum Type {
    S, L, LMS
}

pub struct SuffixArray {
    s: Vec<usize>,
    sa: Vec<usize>
}

impl SuffixArray {
    const CHARS: usize = 1 << 8;

    pub fn new(s: impl Into<String>) -> Self {
        let s = [s.into().bytes().map(|b| b as usize).collect(), vec![0]].concat();
        let mut sa = vec![std::usize::MAX; s.len()];
        Self::sa_is(Self::CHARS, &s, &mut sa);

        Self { s, sa }
    }

    fn sa_is(kinds: usize, s: &[usize], sa: &mut Vec<usize>) {
        let mut types = vec![Type::S; s.len()];
        let mut lms_indices = vec![vec![]; kinds];
        let mut char_num = vec![0; kinds];

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
                    lms_indices[*nc].push(i+1);
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
        let mut lms_indices = vec![std::usize::MAX; s.len()];
        for index in sa.iter().take(s.len()).filter(|index| types[**index] == Type::LMS) {
            if lms_prev == (std::usize::MAX, std::usize::MAX) {
                lms_prev = (*index, *index);
                lms_indices[*index] = rank;
                lms_perm.push(*index);
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
                lms_perm.push(l);
            }
        }

        let lms_indices = if lms_perm.len() == rank+1 {
            lms_perm
        } else {
            let (restore_index, lms_ranks) = lms_indices
                    .into_iter()
                    .enumerate()
                    .filter(|(_, c)| *c != std::usize::MAX)
                    .unzip::<usize, usize, Vec<usize>, Vec<usize>>();
            Self::sa_is(rank + 1, &lms_ranks, sa);
            sa.into_iter()
                .take(lms_ranks.len())
                .map(|i| restore_index[*i])
                .collect()
        };

        Self::induced_sort(&lms_indices, &char_start, &char_num, s, &types, sa);
    }

    fn induced_sort(lms_indices: &[usize], char_start: &[usize], char_num: &[usize], s: &[usize], types: &[Type], sa: &mut Vec<usize>) {
        let kinds = char_start.len();
        sa.iter_mut().take(s.len()).for_each(|sa| *sa = std::usize::MAX);
        sa[0] = s.len() - 1;

        let mut checked = 1;
        let mut filled = vec![0; kinds];
        for (i, lms) in lms_indices.into_iter().enumerate() {
            let c = s[*lms];

            if i > 0 && c != s[lms_indices[i-1]] {
                let target = char_start[c] + char_num[c] - 1;

                while checked <= target {
                    if sa[checked] != std::usize::MAX && sa[checked] > 0 && types[sa[checked]-1] == Type::L {
                        let nc = s[sa[checked]-1];
                        sa[char_start[nc] + filled[nc]] = sa[checked] - 1;
                        filled[nc] += 1;
                    }

                    checked += 1;
                }
            }

            if types[*lms-1] == Type::L {
                let nc = s[*lms-1];
                sa[char_start[nc] + filled[nc]] = *lms - 1;
                filled[nc] += 1;
            }
        }

        for i in checked..s.len() {
            if sa[i] != std::usize::MAX && sa[i] > 0 && types[sa[i]-1] == Type::L {
                let c = s[sa[i]-1];
                sa[char_start[c] + filled[c]] = sa[i] - 1;
                filled[c] += 1;

                if i != 0 && sa[i] != std::usize::MAX && types[sa[i]] != Type::L {
                    sa[i] = std::usize::MAX;
                }
            }
        }

        let mut filled = vec![0; kinds];
        for i in (0..s.len()).rev() {
            if sa[i] != std::usize::MAX && sa[i] > 0 && types[sa[i]-1] != Type::L {
                let c = s[sa[i]-1];
                sa[char_start[c] + char_num[c] - 1 - filled[c]] = sa[i] - 1;
                filled[c] += 1;
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

// AI: Implement Suffix array, Suffix tree, Rolling Hash ....

#[cfg(test)]
mod tests {
    use crate::utility::{
        SuffixArray
    };

    #[test]
    fn suffix_array_test() {
        let sample: &'static str = "mmiissiissiippii";
        let sa = SuffixArray::new(sample);
        assert_eq!(sa.sa, vec![16, 15, 14, 10, 6, 2, 11, 7, 3, 1, 0, 13, 12, 9, 5, 8, 4]);
        let lcpa = sa.lcp_array();
        assert_eq!(lcpa, vec![1, 2, 2, 6, 1, 1, 5, 0, 1, 0, 1, 0, 3, 1, 4]);

        let sample: &'static str = "abracadabra";
        let sa = SuffixArray::new(sample);
        assert_eq!(sa.sa, vec![11, 10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2]);
        let lcpa = sa.lcp_array();
        assert_eq!(lcpa, vec![1, 4, 1, 1, 0, 3, 0, 0, 0, 2]);

        let sample: &'static str = "ababacaca";
        let sa = SuffixArray::new(sample);
        assert_eq!(sa.sa, vec![9, 8, 0, 2, 6, 4, 1, 3, 7, 5]);

        let sample: &'static str = "iqwfmiwjua";
        let sa = SuffixArray::new(sample);
        assert_eq!(sa.sa, vec![10, 9, 3, 0, 5, 7, 4, 1, 8, 2, 6]);

        let sample: &'static str = "caamclyoemcpxfzhdixt";
        let sa = SuffixArray::new(sample);
        assert_eq!(sa.sa, vec![20, 1, 2, 0, 4, 10, 16, 8, 13, 15, 17, 5, 3, 9, 7, 11, 19, 12, 18, 6, 14]);
    }
}
