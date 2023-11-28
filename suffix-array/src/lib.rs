#![allow(clippy::comparison_chain, clippy::upper_case_acronyms)]

use std::collections::BTreeMap;
use std::marker::PhantomData;
use std::mem::ManuallyDrop;
use std::ops::{Index, IndexMut};

pub trait IndexMap<T> {
    fn kinds(&self) -> usize;
    fn to_u32(&self, from: &T) -> u32;
    fn to_usize(&self, from: &T) -> usize;
}

pub struct IdentityMap<T: Ord>(usize, PhantomData<T>);

pub struct SparseMap<'a, T: Ord> {
    map: BTreeMap<&'a T, u32>,
}

macro_rules! impl_index_map {
    ( $( $t:ty ),* ) => {
        $(
            impl IndexMap<$t> for IdentityMap<$t> {
                #[inline]
                fn kinds(&self) -> usize {
                    self.0
                }
                #[inline]
                fn to_u32(&self, from: & $t) -> u32 {
                    *from as u32
                }
                #[inline]
                fn to_usize(&self, from: & $t) -> usize {
                    *from as usize
                }
            }
        )*
    };
}

impl_index_map!(u8, u16, u32, u64, u128, usize, i8, i16, i32, i64, i128, isize, char);

impl<'a, 'b: 'a, T: Ord + 'b> SparseMap<'a, T> {
    fn from_iter(v: impl Iterator<Item = &'b T>) -> Self {
        let mut map = v.map(|v| (v, 0)).collect::<BTreeMap<&'b T, u32>>();
        map.iter_mut()
            .enumerate()
            .for_each(|(i, kv)| *kv.1 = i as u32);
        Self { map }
    }
}

impl<'a, T: Ord> IndexMap<T> for SparseMap<'a, T> {
    fn kinds(&self) -> usize {
        self.map.len()
    }
    fn to_u32(&self, from: &T) -> u32 {
        *self.map.get(from).unwrap()
    }
    fn to_usize(&self, from: &T) -> usize {
        *self.map.get(from).unwrap() as usize
    }
}

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

struct Buckets {
    len: usize,
    sa: ManuallyDrop<*mut u32>,
    bucket: Vec<BucketInfo>,
}

impl Buckets {
    fn new(char_num: Vec<u32>, sa: &mut [u32]) -> Self {
        let mut now = 0;
        let len = sa.len();
        let sa = ManuallyDrop::new(sa.as_mut_ptr());
        Buckets {
            len,
            sa,
            bucket: char_num
                .into_iter()
                .map(|c| {
                    let res = BucketInfo { front: 0, back: 0, start: now };
                    now += c;
                    res
                })
                .collect(),
        }
    }

    fn get(&self, bucket: usize, index: usize) -> u32 {
        let index = unsafe { self.bucket.get_unchecked(bucket) }.start as usize + index;
        unsafe { *self.sa.add(index) }
    }

    fn get_back(&self, bucket: usize, index: usize) -> u32 {
        let index = self
            .bucket
            .get(bucket + 1)
            .map_or(self.len, |b| b.start as usize)
            - 1
            - index;
        unsafe { *self.sa.add(index) }
    }

    fn reset(&mut self) {
        self.bucket.iter_mut().for_each(|b| {
            b.front = 0;
            b.back = 0;
        });
    }

    fn push_front(&mut self, index: usize, val: u32) {
        unsafe {
            *self.sa.add(
                self.bucket.get_unchecked(index).start as usize
                    + self.bucket.get_unchecked(index).front as usize,
            ) = val;
            self.bucket.get_unchecked_mut(index).front += 1;
        }
    }

    fn push_back(&mut self, index: usize, val: u32) {
        let next_start = self
            .bucket
            .get(index + 1)
            .map_or(self.len, |b| b.start as usize);
        unsafe {
            self.bucket.get_unchecked_mut(index).back += 1;
            *self
                .sa
                .add(next_start - self.bucket.get_unchecked(index).back as usize) = val;
        }
    }
}

impl Index<usize> for Buckets {
    type Output = BucketInfo;
    fn index(&self, index: usize) -> &Self::Output {
        unsafe { self.bucket.get_unchecked(index) }
    }
}

impl IndexMut<usize> for Buckets {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        unsafe { self.bucket.get_unchecked_mut(index) }
    }
}

#[repr(C)]
#[derive(Debug, Clone, Copy)]
struct BucketInfo {
    front: u32,
    back: u32,
    start: u32,
}

const THRESHOLD_NAIVE: usize = 10;

#[inline]
fn sa_naive<T: Ord>(s: &[T], sa: &mut [u32]) {
    sa.iter_mut()
        .take(s.len())
        .enumerate()
        .for_each(|(i, v)| *v = i as u32);
    sa[0..s.len()].sort_by_key(|i| &s[*i as usize..]);
}

fn sa_is<T: Ord>(s: &[T], sa: &mut [u32], map: &impl IndexMap<T>) {
    if s.len() <= THRESHOLD_NAIVE {
        sa_naive(s, sa);
        return;
    }

    let mut lms_prev = s.len() as u32 - 1;
    let mut lms_next = vec![u32::MAX; s.len()];

    let mut types = vec![Type::S; s.len()];
    types[s.len() - 1] = Type::L;

    let mut char_num = vec![0; map.kinds()];
    char_num[map.to_usize(s.last().unwrap())] = 1;

    for (i, c) in s.windows(2).enumerate().rev() {
        char_num[map.to_usize(&c[0])] += 1;

        types[i] = if c[0] < c[1] {
            Type::S
        } else if c[0] > c[1] {
            if types[i + 1] == Type::S {
                types[i + 1] = Type::LMS;
                lms_next[i + 1] = lms_prev;
                lms_prev = i as u32 + 1;
            }
            Type::L
        } else {
            types[i + 1]
        };
    }

    let mut lms_indices = types
        .iter()
        .enumerate()
        .filter(|&(_, &t)| t == Type::LMS)
        .map(|(i, _)| i as u32)
        .collect::<Vec<_>>();

    let mut buckets = Buckets::new(char_num, sa);

    // Calculate Pseudo SA
    let max_lms_num = induced_sort(&lms_indices, &mut buckets, s, &types, sa, map);

    // If there is only one LMS-Type(tailling '\0') and the type[0] one is not S-Type, there is no need for a second sort
    // since the order of operations of the sort is unique since all elements except the last element are L-Types.
    if lms_indices.is_empty() && types[0] != Type::S {
        return;
    }
    // If there is only one LMS-Type for each bucket per character type, then a second sort is not necessary
    // because the order of the sorting operations is unique.
    if max_lms_num <= 1 {
        return;
    }

    let mut rank = 0;
    let mut lms_prev = (usize::MAX, usize::MAX);
    let mut lms_ranks = lms_next;
    for (i, index) in sa
        .iter()
        .take(s.len())
        .filter(|&&index| types[index as usize] == Type::LMS)
        .map(|index| *index as usize)
        .enumerate()
    {
        lms_indices[i] = index as u32;
        let (l, r) = (index, lms_ranks[index] as usize);
        let (pl, pr) = lms_prev;
        if pr - pl != r - l || s[pl..pr + 1] != s[l..r + 1] {
            rank += 1;
            lms_prev = (l, r);
        }
        lms_ranks[index] = rank as u32 - 1;
    }

    if lms_indices.len() != rank + 1 {
        let (restore_index, new_s) = lms_ranks
            .into_iter()
            .take(s.len())
            .enumerate()
            .filter(|(_, c)| c != &u32::MAX)
            .map(|(i, c)| (i as u32, c))
            .unzip::<u32, u32, Vec<u32>, Vec<u32>>();
        sa_is(&new_s, sa, &IdentityMap(rank + 1, PhantomData));
        lms_indices
            .iter_mut()
            .zip(sa.iter())
            .for_each(|(lms, i)| *lms = restore_index[*i as usize]);
    };

    buckets.reset();
    induced_sort(&lms_indices, &mut buckets, s, &types, sa, map);
}

#[inline]
fn induced_sort<T: Ord>(
    lms_indices: &[u32],
    buckets: &mut Buckets,
    s: &[T],
    types: &[Type],
    sa: &mut [u32],
    map: &impl IndexMap<T>,
) -> u32 {
    let kinds = map.kinds();

    lms_indices
        .iter()
        .map(|&lms| (lms, map.to_u32(&s[lms as usize])))
        .for_each(|(lms, c)| {
            buckets.push_back(c as usize, lms);
        });

    let mut max_lms_num = 0;
    {
        let nc = map.to_usize(&s[s.len() - 1]);
        buckets.push_front(nc, s.len() as u32 - 1);
    }

    for bucket_index in 0..kinds {
        let filled_lms = buckets[bucket_index].back;
        let mut checked = 0;
        while checked < buckets[bucket_index].front as usize {
            let now = buckets.get(bucket_index, checked);
            if now > 0 && types[now as usize - 1] == Type::L {
                let nc = map.to_usize(&s[now as usize - 1]);
                buckets.push_front(nc, now - 1);
            }
            checked += 1;
        }

        for lms_index in 0..filled_lms as usize {
            let lms = buckets.get_back(bucket_index, lms_index) as usize;
            if lms > 0 && types[lms - 1] == Type::L {
                let nc = map.to_usize(&s[lms - 1]);
                buckets.push_front(nc, lms as u32 - 1);
            }
        }

        max_lms_num = max_lms_num.max(filled_lms);
    }

    // If there is only one LMS-Type and the type[0] one is not S-Type, there is no need for a second sort
    // since the order of operations of the sort is unique since all elements except the last element are L-Types.
    if lms_indices.is_empty() && types[0] != Type::S {
        return max_lms_num;
    }

    buckets.reset();
    // Because sa is used around, s.len() and sa.len() are not always equal.
    for &sa in sa
        .iter()
        .take(s.len())
        .rev()
        .filter(|&&sa| (1..u32::MAX).contains(&sa) && types[sa as usize - 1] != Type::L)
    {
        let c = map.to_usize(&s[sa as usize - 1]);
        buckets.push_back(c, sa - 1);
    }

    max_lms_num
}

////////////////////////////////////////////////////////////////////////////////
// Suffix Array
////////////////////////////////////////////////////////////////////////////////

pub struct SuffixArray<'a, T = u8> {
    s: &'a [T],
    sa: Vec<u32>,
}

impl<'a, T> SuffixArray<'a, T>
where
    T: Ord,
    IdentityMap<T>: IndexMap<T>,
{
    pub fn from_int_slice(v: &'a [T], dense: bool) -> Self {
        let mut sa = vec![u32::MAX; v.len()];

        if sa.len() <= THRESHOLD_NAIVE {
            sa_naive(v, &mut sa);
            return Self { s: v, sa };
        }

        if dense {
            sa_is(v, &mut sa, &IdentityMap(v.len(), PhantomData));
        } else {
            let map = SparseMap::from_iter(v.iter());
            sa_is(v, &mut sa, &map);
        }

        Self { s: v, sa }
    }
}

impl<'a> SuffixArray<'a> {
    const CHARS: usize = 1 << 8;

    pub fn new(s: &'a str) -> Self {
        let s = s.as_bytes();
        let mut sa = vec![u32::MAX; s.len()];

        if sa.len() <= THRESHOLD_NAIVE {
            sa_naive(s, &mut sa);
            return Self { s, sa };
        }

        sa_is(s, &mut sa, &IdentityMap(Self::CHARS, PhantomData));

        Self { s, sa }
    }

    #[inline]
    pub fn get(&self, index: usize) -> usize {
        self.sa[index] as usize
    }

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
            while (lcp + pos_l as usize) < self.s.len()
                && (lcp + pos_r as usize) < self.s.len()
                && self.s[lcp + pos_l as usize] == self.s[lcp + pos_r as usize]
            {
                lcp += 1;
            }
            lcpa[index] = lcp;

            lcp = lcp.saturating_sub(1);
        }
        lcpa
    }

    pub fn iter(&'a self) -> Iter<'a> {
        Iter { iter: self.sa.iter() }
    }
}

impl<'a, T> Index<usize> for SuffixArray<'a, T> {
    type Output = u32;
    fn index(&self, index: usize) -> &Self::Output {
        &self.sa[index]
    }
}

impl<'a, T> IntoIterator for SuffixArray<'a, T> {
    type Item = u32;
    type IntoIter = std::vec::IntoIter<u32>;
    fn into_iter(self) -> Self::IntoIter {
        self.sa.into_iter()
    }
}

pub struct Iter<'a> {
    iter: std::slice::Iter<'a, u32>,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a u32;
    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next()
    }
}

#[cfg(test)]
mod tests {
    use crate::SuffixArray;

    #[test]
    fn suffix_array_test() {
        let sample: &'static str = "mmiissiissiippii";
        let sa = SuffixArray::new(sample);
        assert_eq!(
            sa.sa,
            vec![15, 14, 10, 6, 2, 11, 7, 3, 1, 0, 13, 12, 9, 5, 8, 4]
        );
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
        assert_eq!(
            sa.sa,
            vec![1, 2, 0, 4, 10, 16, 8, 13, 15, 17, 5, 3, 9, 7, 11, 19, 12, 18, 6, 14]
        );

        let sample: &'static str = "kamyucteqzhrvqcbnanikykphkjolv";
        let sa = SuffixArray::new(sample);
        assert_eq!(
            sa.sa,
            vec![
                1, 17, 15, 14, 5, 7, 24, 10, 19, 26, 0, 25, 22, 20, 28, 2, 16, 18, 27, 23, 13, 8,
                11, 6, 4, 29, 12, 21, 3, 9
            ]
        )
    }
}
