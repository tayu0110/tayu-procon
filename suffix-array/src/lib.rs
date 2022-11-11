////////////////////////////////////////////////////////////////////////////////
// Suffix Array
////////////////////////////////////////////////////////////////////////////////
pub struct SuffixArray<'a, T = u8> {
    s: &'a [T],
    sa: Vec<u32>
}
    
// impl SuffixArray {
impl<'a> SuffixArray<'a> {
    // s[i] := A suffix of the string 's' that begins from i-th element. (0 <= i < s.len()-1)
    //      S   : s[i] < s[i+1]
    //      L   : s[i] > s[i+1]
    //      LMS : s[i-1] = L-type && s[i] = S-type (Left-Most-S)
    const S_TYPE: u8 = 0;
    const L_TYPE: u8 = 1;
    const CHARS: usize = 1 << 8;
    const THRESHOLD_NAIVE: usize = 10;
    const TYPE_DECODE_MASK: [u8; 8] = [1, 2, 4, 8, 16, 32, 64, 128];

    pub fn new(s: &'a str) -> Self {
        let s = s.as_bytes();
        let mut sa = vec![std::u32::MAX; s.len()];

        if sa.len() <= Self::THRESHOLD_NAIVE {
            Self::sa_naive(s, &mut sa);
            return Self { s, sa };
        }

        Self::sa_is(Self::CHARS, &s, &mut sa, &mut vec![]);

        Self { s, sa }
    }

    #[inline]
    fn sa_naive<T: Ord>(s: &[T], sa: &mut [u32]) {
        sa.iter_mut().take(s.len()).enumerate().for_each(|(i, v)| *v = i as u32);
        sa[0..s.len()].sort_by_key(|i| &s[*i as usize..]);
    }

    #[inline]
    fn decode_type(index: usize, types: &[u8]) -> u8 {
        (types[index >> 3] & Self::TYPE_DECODE_MASK[index & 0b111]) >> (index & 0b111)
    }

    #[inline]
    fn is_lms(index: usize, types: &[u8]) -> bool {
        index > 0 && Self::decode_type(index, &types) == Self::S_TYPE && Self::decode_type(index-1, &types) == Self::L_TYPE
    }

    fn sa_is<T: Clone + Copy + Ord + std::convert::Into<u32>>(kinds: usize, s: &[T], sa: &mut [u32], lms_next: &mut Vec<u32>) {
        if s.len() <= Self::THRESHOLD_NAIVE {
            Self::sa_naive(s, sa);
            return;
        }

        let mut lms_prev = s.len() as u32 - 1;
        if lms_next.len() < s.len() {
            *lms_next = vec![std::u32::MAX; s.len()];
        }
        let mut types = vec![Self::S_TYPE; (s.len() + 7) >> 3];
        let mut lms_indices = vec![];
        let mut char_start = vec![0u32; kinds+1];

        for (i, cv) in s.chunks(8).enumerate().rev() {
            let ni = i << 3;
            let mut type_collect = 0;
            let mut prev_type = Self::decode_type(std::cmp::min((i+1) << 3, s.len() - 1), &types);
            for (j, c) in cv.iter().enumerate().rev() {
                let nj = ni | j;
                char_start[(*c).into() as usize + 1] += 1;
                lms_next[nj] = std::u32::MAX;
    
                if nj == s.len() - 1 {
                    type_collect = Self::L_TYPE;
                    prev_type = Self::L_TYPE;
                    continue;
                }
                
                let nc = &s[nj+1];
                let t = if c < nc {
                    Self::S_TYPE
                } else if c > nc {
                    if prev_type == Self::S_TYPE {
                        lms_indices.push(nj as u32 + 1);
                        lms_next[nj+1] = lms_prev;
                        lms_prev = nj as u32 + 1;
                    }
                    Self::L_TYPE
                } else {
                    prev_type
                };
                type_collect = (type_collect << 1) | t;
                prev_type = t;
            }
            types[i] = type_collect;
        }

        for i in 0..kinds {
            char_start[i+1] += char_start[i];
        }

        // Calculate Pseudo SA
        let max_lms_num = Self::induced_sort(&lms_indices, &char_start, s, &types, sa);

        // If there is only one LMS-Type(tailling '\0') and the type[0] one is not S-Type, there is no need for a second sort
        // since the order of operations of the sort is unique since all elements except the last element are L-Types.
        if lms_indices.len() == 0 && Self::decode_type(0, &types) != Self::S_TYPE {
            return;
        }
        // If there is only one LMS-Type for each bucket per character type, then a second sort is not necessary
        // because the order of the sorting operations is unique.
        if max_lms_num <= 1 {
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
    fn induced_sort<T: Clone + Copy + Ord + std::convert::Into<u32>>(lms_indices: &[u32], char_start: &[u32], s: &[T], types: &[u8], sa: &mut [u32]) -> u32 {    
        let kinds = char_start.len() - 1;

        let mut filled_lms = vec![0; kinds];
        lms_indices.into_iter().map(|lms| (*lms, s[*lms as usize].into())).for_each(|(lms, c)| {
            sa[(char_start[c as usize + 1] - 1 - filled_lms[c as usize]) as usize] = lms;
            filled_lms[c as usize] += 1;
        });

        let mut max_lms_num = 0;
        let mut filled = vec![0; kinds];
        {
            let nc = s[s.len() - 1].into();
            sa[char_start[nc as usize] as usize] = s.len() as u32 - 1;
            filled[nc as usize] += 1;
        }

        for backet_index in 0..kinds {
            let mut rem = filled[backet_index];
            let mut checked = char_start[backet_index] as usize;
            while rem > 0 {
                if sa[checked] > 0 && Self::decode_type(sa[checked] as usize - 1, &types) == Self::L_TYPE {
                    let nc = s[sa[checked] as usize - 1].into();
                    sa[(char_start[nc as usize]  + filled[nc as usize]) as usize] = sa[checked] - 1;
                    filled[nc as usize] += 1;
                    if backet_index == nc as usize {
                        rem += 1;
                    }
                }
                checked += 1;
                rem -= 1;
            }

            for lms_index in 0..filled_lms[backet_index] {
                let lms = sa[(char_start[backet_index+1] - 1 - lms_index) as usize] as usize;
                if lms > 0 && Self::decode_type(lms - 1, &types) == Self::L_TYPE {
                    let nc = s[lms - 1].into();
                    sa[(char_start[nc as usize] + filled[nc as usize]) as usize] = lms as u32 - 1;
                    filled[nc as usize] += 1;
                }
            }

            max_lms_num = std::cmp::max(max_lms_num, filled_lms[backet_index]);
            filled[backet_index] = 0;
        }

        // If there is only one LMS-Type and the type[0] one is not S-Type, there is no need for a second sort
        // since the order of operations of the sort is unique since all elements except the last element are L-Types.
        if lms_indices.len() == 0 && Self::decode_type(0, &types) != Self::S_TYPE {
            return max_lms_num;
        }

        for i in (0..s.len()).rev() {
            if sa[i] != std::u32::MAX && sa[i] > 0 && Self::decode_type(sa[i] as usize - 1, &types) != Self::L_TYPE {
                let c: u32 = s[sa[i] as usize - 1].into();
                sa[(char_start[c as usize + 1] - 1 - filled[c as usize]) as usize] = sa[i] - 1;
                filled[c as usize] += 1;
            }
        }

        max_lms_num
    }

    #[inline]
    pub fn get_sa(&self) -> &[u32] {
        &self.sa
    }

    /// LCPA\[i\] := Longest Common Prefix between s\[sa\[i\]\] and s\[sa\[i+1\]\]
    pub fn lcp_array(&self) -> Vec<usize> {
        let mut rank = vec![0; self.sa.len()];
        for (i, sa) in self.sa.iter().enumerate() {
            rank[*sa as usize] = i;
        }

        let mut lcp = 0;
        let mut lcpa = vec![0; self.sa.len()-1];
        for index in rank {
            if index == self.sa.len() - 1 {
                lcp = 0;
                continue;
            }
        
            let (pos_l, pos_r) = (self.sa[index], self.sa[index+1]);
            while (lcp + pos_l as usize) < self.s.len() && (lcp + pos_r as usize) < self.s.len() && self.s[lcp + pos_l as usize] == self.s[lcp + pos_r as usize] {
                    lcp += 1;
            }
            lcpa[index] = lcp;

            lcp = lcp.saturating_sub(1);
        }
        lcpa
    }
}

// AI: Implement Suffix array, Suffix tree, Rolling Hash ....

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
        assert_eq!(sa.sa, vec![1, 17, 15, 14, 5, 7, 24, 10, 19, 26, 0, 25, 22, 20, 28, 2, 16, 18, 27, 23, 13, 8, 11, 6, 4, 29, 12, 21, 3, 9])
    }
}
