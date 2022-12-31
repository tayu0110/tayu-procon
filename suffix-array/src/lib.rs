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
    S,
    L,
    LMS,
}

pub struct SuffixArray<'a, T = u8> {
    s: &'a [T],
    sa: Vec<u32>,
}

impl<'a> SuffixArray<'a> {
    const CHARS: usize = 1 << 8;
    const THRESHOLD_NAIVE: usize = 10;

    pub fn new(s: &'a str) -> Self {
        let s = s.as_bytes();
        let mut sa = vec![std::u32::MAX; s.len()];

        if sa.len() <= Self::THRESHOLD_NAIVE {
            Self::sa_naive(s, &mut sa);
            return Self { s, sa };
        }

        unsafe {
            Self::sa_is(Self::CHARS, &s, &mut sa);
        }

        Self { s, sa }
    }

    #[inline]
    fn sa_naive<T: Ord>(s: &[T], sa: &mut [u32]) {
        sa.iter_mut().take(s.len()).enumerate().for_each(|(i, v)| *v = i as u32);
        sa[0..s.len()].sort_by_key(|i| &s[*i as usize..]);
    }

    unsafe fn sa_is<T: Clone + Copy + Ord + std::convert::Into<u32>>(kinds: usize, s: &[T], sa: &mut [u32]) {
        if s.len() <= Self::THRESHOLD_NAIVE {
            Self::sa_naive(s, sa);
            return;
        }

        let mut lms_prev = s.len() as u32 - 1;
        let mut lms_next = vec![std::u32::MAX; s.len()];

        let mut types = vec![Type::S; s.len()];
        types[s.len() - 1] = Type::L;

        let mut char_start = vec![0u32; kinds + 1];
        char_start[(*s.last().unwrap()).into() as usize + 1] = 1;

        for (i, c) in s.windows(2).enumerate().rev() {
            *char_start.get_unchecked_mut((*c.get_unchecked(0)).into() as usize + 1) += 1;

            *types.get_unchecked_mut(i) = if c.get_unchecked(0) < c.get_unchecked(1) {
                Type::S
            } else if c.get_unchecked(0) > c.get_unchecked(1) {
                if types.get_unchecked(i + 1) == &Type::S {
                    *types.get_unchecked_mut(i + 1) = Type::LMS;
                    *lms_next.get_unchecked_mut(i + 1) = lms_prev;
                    lms_prev = i as u32 + 1;
                }
                Type::L
            } else {
                *types.get_unchecked(i + 1)
            };
        }

        let mut lms_indices = types.iter().enumerate().filter(|(_, t)| t == &&Type::LMS).map(|(i, _)| i as u32).collect::<Vec<_>>();

        for i in 0..kinds {
            *char_start.get_unchecked_mut(i + 1) += *char_start.get_unchecked(i);
        }

        // Calculate Pseudo SA
        let max_lms_num = Self::induced_sort(&lms_indices, &char_start, s, &types, sa);

        // If there is only one LMS-Type(tailling '\0') and the type[0] one is not S-Type, there is no need for a second sort
        // since the order of operations of the sort is unique since all elements except the last element are L-Types.
        if lms_indices.len() == 0 && types[0] != Type::S {
            return;
        }
        // If there is only one LMS-Type for each bucket per character type, then a second sort is not necessary
        // because the order of the sorting operations is unique.
        if max_lms_num <= 1 {
            return;
        }

        let mut rank = 0;
        let mut lms_prev = (std::usize::MAX, std::usize::MAX);
        let mut lms_ranks = lms_next;
        for (i, &index) in sa.iter().take(s.len()).filter(|&&index| types.get_unchecked_mut(index as usize) == &Type::LMS).enumerate() {
            *lms_indices.get_unchecked_mut(i) = index;
            let (l, r) = (index as usize, *lms_ranks.get_unchecked(index as usize) as usize);
            let (pl, pr) = lms_prev;
            if pr - pl != r - l || s[pl..pr + 1] != s[l..r + 1] {
                rank += 1;
                lms_prev = (l, r);
            }
            *lms_ranks.get_unchecked_mut(index as usize) = rank - 1;
        }

        if lms_indices.len() as u32 != rank + 1 {
            let (restore_index, new_s) = lms_ranks
                .into_iter()
                .take(s.len())
                .enumerate()
                .filter(|(_, c)| c != &std::u32::MAX)
                .map(|(i, c)| (i as u32, c))
                .unzip::<u32, u32, Vec<u32>, Vec<u32>>();
            Self::sa_is(rank as usize + 1, &new_s, sa);
            lms_indices
                .iter_mut()
                .zip(sa.into_iter())
                .for_each(|(lms, i)| *lms = *restore_index.get_unchecked(*i as usize));
        };

        Self::induced_sort(&lms_indices, &char_start, s, &types, sa);
    }

    #[inline]
    unsafe fn induced_sort<T: Clone + Copy + Ord + std::convert::Into<u32>>(lms_indices: &[u32], char_start: &[u32], s: &[T], types: &[Type], sa: &mut [u32]) -> u32 {
        let kinds = char_start.len() - 1;

        let mut filled_lms = vec![0; kinds];
        lms_indices.into_iter().map(|&lms| (lms, (*s.get_unchecked(lms as usize)).into())).for_each(|(lms, c)| {
            *sa.get_unchecked_mut((*char_start.get_unchecked(c as usize + 1) - 1 - *filled_lms.get_unchecked(c as usize)) as usize) = lms;
            *filled_lms.get_unchecked_mut(c as usize) += 1;
        });

        let mut max_lms_num = 0;
        let mut filled = vec![0; kinds];
        {
            let nc = s[s.len() - 1].into() as usize;
            sa[char_start[nc] as usize] = s.len() as u32 - 1;
            filled[nc] += 1;
        }

        for backet_index in 0..kinds {
            let mut rem = *filled.get_unchecked(backet_index);
            let mut checked = *char_start.get_unchecked(backet_index) as usize;
            while rem > 0 {
                if sa.get_unchecked(checked) > &0 && types.get_unchecked(*sa.get_unchecked(checked) as usize - 1) == &Type::L {
                    let nc = (*s.get_unchecked(*sa.get_unchecked(checked) as usize - 1)).into() as usize;
                    *sa.get_unchecked_mut((*char_start.get_unchecked(nc) + *filled.get_unchecked(nc)) as usize) = *sa.get_unchecked(checked) - 1;
                    *filled.get_unchecked_mut(nc) += 1;
                    if backet_index == nc {
                        rem += 1;
                    }
                }
                checked += 1;
                rem -= 1;
            }

            for lms_index in 0..filled_lms[backet_index] {
                let lms = *sa.get_unchecked((*char_start.get_unchecked(backet_index + 1) - 1 - lms_index) as usize) as usize;
                if lms > 0 && types.get_unchecked(lms - 1) == &Type::L {
                    let nc = (*s.get_unchecked(lms - 1)).into() as usize;
                    *sa.get_unchecked_mut((*char_start.get_unchecked(nc) + *filled.get_unchecked(nc)) as usize) = lms as u32 - 1;
                    *filled.get_unchecked_mut(nc) += 1;
                }
            }

            max_lms_num = std::cmp::max(max_lms_num, *filled_lms.get_unchecked(backet_index));
            *filled.get_unchecked_mut(backet_index) = 0;
        }

        // If there is only one LMS-Type and the type[0] one is not S-Type, there is no need for a second sort
        // since the order of operations of the sort is unique since all elements except the last element are L-Types.
        if lms_indices.len() == 0 && types[0] != Type::S {
            return max_lms_num;
        }

        for i in (0..s.len()).rev() {
            if sa.get_unchecked(i) != &std::u32::MAX && sa.get_unchecked(i) > &0 && types.get_unchecked(*sa.get_unchecked(i) as usize - 1) != &Type::L {
                let c = (*s.get_unchecked(*sa.get_unchecked(i) as usize - 1)).into() as usize;
                *sa.get_unchecked_mut((*char_start.get_unchecked(c + 1) - 1 - *filled.get_unchecked(c)) as usize) = *sa.get_unchecked(i) - 1;
                *filled.get_unchecked_mut(c) += 1;
            }
        }

        max_lms_num
    }

    #[inline]
    pub fn get_sa(&self) -> &[u32] { &self.sa }

    /// LCPA\[i\] := Longest Common Prefix between s\[sa\[i\]\] and s\[sa\[i+1\]\]
    pub fn lcp_array(&self) -> Vec<usize> {
        let mut rank = vec![0; self.sa.len()];
        for (i, sa) in self.sa.iter().enumerate() {
            rank[*sa as usize] = i;
        }

        let mut lcp = 0;
        let mut lcpa = vec![0; self.sa.len() - 1];
        for index in rank {
            if index == self.sa.len() - 1 {
                lcp = 0;
                continue;
            }

            let (pos_l, pos_r) = (self.sa[index], self.sa[index + 1]);
            while (lcp + pos_l as usize) < self.s.len() && (lcp + pos_r as usize) < self.s.len() && self.s[lcp + pos_l as usize] == self.s[lcp + pos_r as usize] {
                lcp += 1;
            }
            lcpa[index] = lcp;

            lcp = lcp.saturating_sub(1);
        }
        lcpa
    }
}

#[cfg(test)]
mod tests {
    use crate::SuffixArray;

    #[test]
    fn suffix_array_test() {
        let sample: &'static str = "mmiissiissiippii";
        let sa = SuffixArray::new(sample);
        assert_eq!(sa.sa, vec![15, 14, 10, 6, 2, 11, 7, 3, 1, 0, 13, 12, 9, 5, 8, 4]);
        let lcpa = sa.lcp_array();
        assert_eq!(lcpa, vec![1, 2, 2, 6, 1, 1, 5, 0, 1, 0, 1, 0, 3, 1, 4]);

        let sample: &'static str = "abracadabra";
        let sa = SuffixArray::new(sample);
        assert_eq!(sa.sa, vec![10, 7, 0, 3, 5, 8, 1, 4, 6, 9, 2]);
        let lcpa = sa.lcp_array();
        assert_eq!(lcpa, vec![1, 4, 1, 1, 0, 3, 0, 0, 0, 2]);

        let sample: &'static str = "ababacaca";
        let sa = SuffixArray::new(sample);
        assert_eq!(sa.sa, vec![8, 0, 2, 6, 4, 1, 3, 7, 5]);

        let sample: &'static str = "iqwfmiwjua";
        let sa = SuffixArray::new(sample);
        assert_eq!(sa.sa, vec![9, 3, 0, 5, 7, 4, 1, 8, 2, 6]);

        let sample: &'static str = "caamclyoemcpxfzhdixt";
        let sa = SuffixArray::new(sample);
        assert_eq!(sa.sa, vec![1, 2, 0, 4, 10, 16, 8, 13, 15, 17, 5, 3, 9, 7, 11, 19, 12, 18, 6, 14]);

        let sample: &'static str = "kamyucteqzhrvqcbnanikykphkjolv";
        let sa = SuffixArray::new(sample);
        assert_eq!(
            sa.sa,
            vec![1, 17, 15, 14, 5, 7, 24, 10, 19, 26, 0, 25, 22, 20, 28, 2, 16, 18, 27, 23, 13, 8, 11, 6, 4, 29, 12, 21, 3, 9]
        )
    }
}
