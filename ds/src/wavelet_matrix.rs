use std::collections::{BinaryHeap, HashMap};
use std::ops::{Range, RangeBounds};

use crate::convert_range;

// Assuming the size of `BitVector` is up to u32::MAX, determine LARGE_WIDTH as (lg N)^2
const LARGE_WIDTH: usize = 1024;
// Assuming the size of `BitVector` is up to u32::MAX, determine LARGE_WIDTH as (1/2)(lg N)
const SMALL_WIDTH: usize = 16;

type BitBlock = u16;

const __BLOCK_WIDTH_CONSTRAINT: () = {
    assert!(1 << LARGE_WIDTH.trailing_zeros() == LARGE_WIDTH);
    assert!(1 << SMALL_WIDTH.trailing_zeros() == SMALL_WIDTH);
    assert!(SMALL_WIDTH == BitBlock::BITS as usize);
};

/// Reference : https://miti-7.hatenablog.com/entry/2018/04/15/155638
#[derive(Debug, Clone, PartialEq)]
struct BitVector {
    large: Box<[u32]>,
    small: Box<[u16]>,
    data: Box<[BitBlock]>,
}

impl BitVector {
    fn new(data: Box<[BitBlock]>) -> Self {
        const L: usize = LARGE_WIDTH / BitBlock::BITS as usize;
        let (mut large, mut small) = (
            Vec::with_capacity((data.len() + L - 1) / L + 1),
            Vec::with_capacity(data.len() + 1),
        );
        large.push(0);
        small.push(0);
        for large_block in data.chunks(L) {
            for small_block in large_block {
                small.push(small.last().unwrap() + small_block.count_ones() as u16);
            }
            large.push(large.last().unwrap_or(&0) + *small.last().unwrap() as u32);
            if large_block.len() == L {
                *small.last_mut().unwrap() = 0;
            }
        }

        Self {
            large: large.into_boxed_slice(),
            small: small.into_boxed_slice(),
            data,
        }
    }

    /// Count `B` between 0 to `to`. `to` is exclusive.
    #[doc(alias = "rank")]
    #[target_feature(enable = "popcnt")]
    unsafe fn count<const B: u8>(&self, to: usize) -> usize {
        assert!(B < 2);
        if to == 0 {
            return 0;
        }
        let l = to / LARGE_WIDTH;
        let s = to / SMALL_WIDTH;

        let mut res = self.large[l] as usize + self.small[s] as usize;

        let rem = to & (SMALL_WIDTH - 1);
        if rem > 0 {
            res += self.data[s]
                .wrapping_shl(BitBlock::BITS - rem as u32)
                .count_ones() as usize;
        }

        if B == 0 {
            res = to - res;
        }

        res
    }

    /// Return `at`-th bit on data.
    fn access(&self, at: usize) -> u16 {
        (self.data[at / BitBlock::BITS as usize] >> (at % BitBlock::BITS as usize)) & 1
    }

    /// Return the position of `nth`-th `B`.
    ///
    /// # Panics
    /// - `B` must be equal to 0 or 1
    #[doc(alias = "select")]
    fn position_of<const B: u8>(&self, nth: usize) -> usize {
        assert!(B < 2);

        let (mut l, mut r) = (0, self.data.len() * BitBlock::BITS as usize);
        while r - l > 1 {
            let m = (r + l) / 2;
            if unsafe { self.count::<B>(m) } <= nth {
                l = m;
            } else {
                r = m;
            }
        }
        l
    }
}

/// Reference : https://miti-7.hatenablog.com/entry/2018/04/28/152259
#[derive(Debug, Clone)]
pub struct WaveletMatrix<T> {
    len: usize,
    bitvec: Vec<BitVector>,
    bound: Vec<usize>,
    first: HashMap<T, u32>,
}

macro_rules! impl_wavelet_matrix {
    ( $( $t:ty ),* ) => {
        $(
            impl WaveletMatrix<$t> {
                /// Return the length of an original sequence.
                pub const fn len(&self) -> usize {
                    self.len
                }
            
                /// Check `self.len() == 0`
                pub const fn is_empty(&self) -> bool {
                    self.len() == 0
                }
            
                /// Get the `at`-th element of an original sequence.  
                /// If `at >= self.len()` is satisfied, return `None`.
                ///
                /// # Examples
                /// ```rust
                /// use ds::WaveletMatrix;
                ///
                /// let wm = WaveletMatrix::from([0u64, 1, 2, 3, 4]);
                /// assert_eq!(wm.get(0), Some(0));
                /// assert_eq!(wm.get(3), Some(3));
                /// // index out of range
                /// assert!(wm.get(5).is_none());
                /// ```
                #[doc(alias = "access")]
                pub fn get(&self, at: usize) -> Option<$t> {
                    (at < self.len()).then(|| {
                        let mut res = 0;
                        let mut now = at;
                        for (bitvec, bound) in self.bitvec.iter().zip(self.bound.iter()) {
                            let bit = bitvec.access(now) as $t;
                            res = (res << 1) | bit;
                            if bit == 0 {
                                now = unsafe { bitvec.count::<0>(now) };
                            } else {
                                now = bound + unsafe { bitvec.count::<1>(now) };
                            }
                        }
            
                        res
                    })
                }
            
                fn countk_to(&self, k: $t, first: usize, to: usize) -> usize {
                    let mut b = self.bitvec.len();
                    let mut now = to;
                    for (bitvec, bound) in self.bitvec.iter().zip(self.bound.iter()) {
                        b -= 1;
            
                        if (k >> b) & 1 == 0 {
                            now = unsafe { bitvec.count::<0>(now) };
                        } else {
                            now = bound + unsafe { bitvec.count::<1>(now) };
                        }
                    }
            
                    now - first
                }
            
                /// Count the number of `k` that exists within `range`.
                ///
                /// # Panics
                /// - `range` must specify the range within an original sequence.
                ///
                /// # Examples
                /// ```rust
                /// use ds::WaveletMatrix;
                ///
                /// let wm = WaveletMatrix::from([0u64, 1, 0, 2, 1, 1]);
                /// assert_eq!(wm.countk(0, 0..6), 2);
                /// assert_eq!(wm.countk(0, 0..2), 1);
                /// assert_eq!(wm.countk(1, 2..6), 2);
                /// assert_eq!(wm.countk(5, 0..6), 0);
                /// ```
                #[doc(alias = "rank")]
                pub fn countk(&self, k: $t, range: impl RangeBounds<usize>) -> usize {
                    let Some(&first) = self.first.get(&k) else {
                        return 0;
                    };
                    let Range { start, end } = convert_range(self.len(), range);
                    assert!(end <= self.len());
            
                    let mut res = self.countk_to(k, first as usize, end);
                    if start > 0 {
                        res -= self.countk_to(k, first as usize, start);
                    }
            
                    res
                }
            
                /// Get `nth`-th `k` in an original sequence.  
                /// If such an element is not found, return `None`.
                ///
                /// `nth` is 0-index.
                ///
                /// # Examples
                /// ```rust
                /// use ds::WaveletMatrix;
                ///
                /// let wm = WaveletMatrix::from([0u64, 1, 0, 2, 1, 1]);
                /// assert_eq!(wm.position_of(0, 0), Some(0));
                /// assert_eq!(wm.position_of(0, 1), Some(2));
                /// assert_eq!(wm.position_of(0, 2), None);
                /// assert_eq!(wm.position_of(1, 2), Some(5));
                /// assert_eq!(wm.position_of(5, 0), None);
                /// ```
                #[doc(alias = "select")]
                pub fn position_of(&self, mut k: $t, nth: usize) -> Option<usize> {
                    let start = *self.first.get(&k)? as usize;
                    (nth < self.countk(k, ..self.len())).then(|| {
                        let mut now = start + nth;
                        for (bitvec, bound) in self.bitvec.iter().zip(self.bound.iter()).rev() {
                            let bit = k & 1;
                            k >>= 1;
            
                            if bit == 0 {
                                now = bitvec.position_of::<0>(now);
                            } else {
                                now = bitvec.position_of::<1>(now - bound);
                            }
                        }
            
                        now
                    })
                }
            
                /// Get `nth`-th smallest element that exists within `range`.  
                /// If `nth` is longer than the length of `range` or `range` is empty, return `None`.
                ///
                /// `nth` is 0-index.
                ///
                /// # Panics
                /// - `range` must specify the range within an original sequence.
                ///
                /// # Examples
                /// ```rust
                /// use ds::WaveletMatrix;
                ///
                /// let wm = WaveletMatrix::from([0u64, 1, 0, 2, 1, 1]);
                /// assert_eq!(wm.nth_smallest(0, 0..6), Some(0));
                /// assert_eq!(wm.nth_smallest(0, 3..6), Some(1));
                /// assert_eq!(wm.nth_smallest(7, 0..6), None);
                /// ```
                #[doc(alias = "quantile")]
                pub fn nth_smallest(&self, mut nth: usize, range: impl RangeBounds<usize>) -> Option<$t> {
                    let Range { mut start, mut end } = convert_range(self.len(), range);
                    assert!(end <= self.len());
                    (start < end && nth < end - start).then(|| {
                        let mut res = 0;
                        for (bitvec, bound) in self.bitvec.iter().zip(self.bound.iter()) {
                            let zeros_until_end = unsafe { bitvec.count::<0>(end) };
                            let zeros_until_start = unsafe { bitvec.count::<0>(start) };
                            let zeros = zeros_until_end - zeros_until_start;
            
                            res <<= 1;
                            if nth < zeros {
                                (start, end) = (zeros_until_start, zeros_until_end);
                            } else {
                                res |= 1;
                                nth -= zeros;
                                (start, end) = (
                                    bound + start - zeros_until_start,
                                    bound + end - zeros_until_end,
                                );
                            }
                        }
            
                        res
                    })
                }
            
                /// Get `nth`-th smallest element that exists within `range`.  
                /// If `nth` is longer than the length of `range` or `range` is empty, return `None`.
                ///
                /// # Panics
                /// - `range` must specify the range within an original sequence.
                ///
                /// # Examples
                /// ```rust
                /// use ds::WaveletMatrix;
                ///
                /// let wm = WaveletMatrix::from([0u64, 1, 0, 2, 1, 1]);
                /// assert_eq!(wm.nth_largest(0, 0..6), Some(2));
                /// assert_eq!(wm.nth_largest(0, 3..6), Some(2));
                /// assert_eq!(wm.nth_largest(7, 0..6), None);
                /// ```
                pub fn nth_largest(&self, nth: usize, range: impl RangeBounds<usize>) -> Option<$t> {
                    let range = convert_range(self.len(), range);
                    (!range.is_empty() && nth < range.len())
                        .then(|| self.nth_smallest(range.len() - 1 - nth, range).unwrap())
                }
            
                /// Return elements and frequencies within the range indicated by `range` in descending order of frequency.  
                /// Returned tuples represents `(element, frequency)`.
                ///
                /// This method should in some cases result in very poor performance and should be used with care.
                ///
                /// If there are elements with the same frequency, the order of occurrence is *not defined*.
                ///
                /// # Panics
                /// - `range` must specify the range within an original sequence.
                ///
                /// # Examples
                /// ```rust
                /// use ds::WaveletMatrix;
                ///
                /// let wm = WaveletMatrix::from([0u64, 1, 0, 2, 1, 1]);
                /// let mut iter = wm.top_of_mode(..);
                /// assert_eq!(iter.next(), Some((1, 3)));
                /// assert_eq!(iter.next(), Some((0, 2)));
                /// assert_eq!(iter.next(), Some((2, 1)));
                /// assert_eq!(iter.next(), None);
                /// ```
                #[doc(alias = "topk")]
                pub fn top_of_mode(
                    &self,
                    range: impl RangeBounds<usize>,
                ) -> impl Iterator<Item = ($t, usize)> + '_ {
                    let Range { start, end } = convert_range(self.len(), range);
                    assert!(end <= self.len());
            
                    let mut nt = BinaryHeap::new();
                    nt.push((end - start, start, 0, 0));
                    std::iter::from_fn(move || {
                        while let Some((width, start, value, level)) = nt.pop() {
                            if level == self.bitvec.len() {
                                return Some((value, width));
                            }
            
                            let end = width + start;
                            let bitvec = &self.bitvec[level];
                            let zeros_until_end = unsafe { bitvec.count::<0>(end) };
                            let zeros_until_start = unsafe { bitvec.count::<0>(start) };
                            let zeros = zeros_until_end - zeros_until_start;
                            if zeros > 0 {
                                nt.push((zeros, zeros_until_start, value << 1, level + 1));
                            }
                            if width - zeros > 0 {
                                nt.push((
                                    width - zeros,
                                    self.bound[level] + start - zeros_until_start,
                                    (value << 1) | 1,
                                    level + 1,
                                ));
                            }
                        }
            
                        None
                    })
                }
            
                /// Return the sum of elements that exists within `range`.
                ///
                /// Note that performance is worse when most of the elements in the range are distinct.
                ///
                /// # Panics
                /// - `range` must specify the range within an original sequence.
                ///
                /// # Examples
                /// ```rust
                /// use ds::WaveletMatrix;
                ///
                /// let wm = WaveletMatrix::from([0u64, 1, 0, 2, 1, 1]);
                /// assert_eq!(wm.sum(..), 5);
                /// assert_eq!(wm.sum(2..), 4);
                /// assert_eq!(wm.sum(..4), 3);
                /// ```
                pub fn sum(&self, range: impl RangeBounds<usize>) -> $t {
                    self.top_of_mode(range).map(|(v, cnt)| v * cnt as $t).sum()
                }
            }
            
            impl From<Vec<$t>> for WaveletMatrix<$t> {
                fn from(mut value: Vec<$t>) -> Self {
                    let Some(&max) = value.iter().max() else {
                        return Self {
                            len: value.len(),
                            bitvec: vec![],
                            bound: vec![],
                            first: HashMap::new(),
                        };
                    };
            
                    if max == 0 {
                        let len = (value.len() + BitBlock::BITS as usize - 1) / BitBlock::BITS as usize;
                        return Self {
                            len: value.len(),
                            bitvec: vec![BitVector::new(vec![0; len].into_boxed_slice())],
                            bound: vec![value.len()],
                            first: HashMap::from([(0, 0)]),
                        };
                    }
            
                    let width = <$t>::BITS - max.leading_zeros();
                    let mut bitvec = vec![];
                    let mut bound = vec![];
                    let mut working = vec![0; value.len()];
                    for r in (0..width).rev() {
                        let bv = BitVector::new(
                            value
                                .chunks(BitBlock::BITS as usize)
                                .map(|v| v.iter().rev().fold(0u16, |s, v| (s << 1) | ((v >> r) as u16 & 1)))
                                .collect(),
                        );
            
                        bound.push(unsafe { bv.count::<0>(value.len()) });
                        let (mut zeros, mut ones) = (0, *bound.last().unwrap());
                        for &v in &value {
                            if (v >> r) & 1 == 0 {
                                working[zeros] = v;
                                zeros += 1;
                            } else {
                                working[ones] = v;
                                ones += 1;
                            }
                        }
                        (value, working) = (working, value);
                        bitvec.push(bv);
                    }
            
                    let mut first = HashMap::from([(value[0], 0)]);
                    first.extend(
                        value
                            .windows(2)
                            .enumerate()
                            .filter_map(|(i, v)| (v[0] != v[1]).then_some((v[1], i as u32 + 1))),
                    );
            
                    Self { len: value.len(), bitvec, bound, first }
                }
            }
            
            impl From<&[$t]> for WaveletMatrix<$t> {
                fn from(value: &[$t]) -> Self {
                    Self::from(value.to_vec())
                }
            }
            
            impl<const N: usize> From<[$t; N]> for WaveletMatrix<$t> {
                fn from(value: [$t; N]) -> Self {
                    Self::from(&value[..])
                }
            }
            
            impl FromIterator<$t> for WaveletMatrix<$t> {
                fn from_iter<T: IntoIterator<Item = $t>>(iter: T) -> Self {
                    Self::from(iter.into_iter().collect::<Vec<$t>>())
                }
            }
        )*
    };
}

impl_wavelet_matrix!(u8, u16, u32, u64, u128);

#[cfg(test)]
mod tests {
    use rand::{thread_rng, Rng};

    use super::*;

    #[test]
    fn bit_vector_random_test() {
        const S: usize = 128;
        const Q: usize = 100;
        let mut rng = thread_rng();

        for _ in 0..Q {
            let t = (0..S).map(|_| rng.gen()).collect::<Box<[BitBlock]>>();
            let bitvec = BitVector::new(t.clone());

            let mut cnt = [0; 2];
            for i in 0..S {
                for j in 0..BitBlock::BITS as usize {
                    let idx = i * BitBlock::BITS as usize + j;
                    let bit = (t[i] >> j) & 1;
                    eprintln!("i: {i}, j: {j}, idx: {idx}, bit: {bit}");
                    assert_eq!(bitvec.access(idx), bit);

                    if bit == 0 {
                        assert_eq!(bitvec.position_of::<0>(cnt[0]), idx);
                    } else {
                        assert_eq!(bitvec.position_of::<1>(cnt[1]), idx);
                    }

                    assert_eq!(unsafe { bitvec.count::<0>(idx) }, cnt[0]);
                    assert_eq!(unsafe { bitvec.count::<1>(idx) }, cnt[1]);

                    cnt[bit as usize] += 1;
                }
            }

            assert_eq!(
                unsafe { bitvec.count::<0>(S * BitBlock::BITS as usize) },
                cnt[0]
            );
            assert_eq!(
                unsafe { bitvec.count::<1>(S * BitBlock::BITS as usize) },
                cnt[1]
            );
        }
    }

    #[test]
    fn bit_vector_rank_test() {
        let bitvec = BitVector::new(vec![0b0000000001111001].into_boxed_slice());
        assert_eq!(unsafe { bitvec.count::<0>(16) }, 11);
        assert_eq!(unsafe { bitvec.count::<1>(16) }, 5);
    }

    #[test]
    fn wavelet_matrix_simple_queries_test() {
        let wm = WaveletMatrix::from(vec![5u8, 4, 5, 5, 2, 1, 5, 6, 1, 3, 5, 0]);

        assert_eq!(
            wm.bitvec,
            vec![
                BitVector::new(vec![0b010011001111].into_boxed_slice()),
                BitVector::new(vec![0b010000001001].into_boxed_slice()),
                BitVector::new(vec![0b010111101011].into_boxed_slice()),
            ]
        );
        assert_eq!(wm.bound, vec![5, 9, 4]);
        assert_eq!(
            wm.first,
            HashMap::from([(0, 0), (4, 1), (2, 2), (6, 3), (1, 4), (5, 6), (3, 11)])
        );

        assert_eq!(wm.countk(5, ..9), 4);
        assert_eq!(wm.countk(5, ..12), 5);
        assert_eq!(wm.countk(5, ..10), 4);
        assert_eq!(wm.countk(9, ..12), 0);

        assert_eq!(wm.nth_smallest(7, 1..11), Some(5));
        assert_eq!(wm.nth_smallest(0, 1..3), Some(4));
        assert_eq!(wm.nth_smallest(1, 8..12), Some(1));

        assert_eq!(
            wm.top_of_mode(..).take(2).collect::<Vec<_>>(),
            vec![(5, 5), (1, 2)]
        );
    }

    #[test]
    fn wavelet_matrix_access_test() {
        let wm = WaveletMatrix::from([1u8, 4, 0, 1, 3]);

        assert_eq!(wm.get(0), Some(1));
        assert_eq!(wm.get(1), Some(4));
        assert_eq!(wm.get(2), Some(0));
        assert_eq!(wm.get(3), Some(1));
        assert_eq!(wm.get(4), Some(3));
    }

    #[test]
    fn wavelet_matrix_random_countk_test() {
        const Q: usize = 1000;
        const R: usize = 30;
        let mut rng = thread_rng();
        for i in 0..Q {
            eprintln!("---------- start {i}-th iteration ----------");
            let n = rng.gen_range(1..20);
            let v = (0..n).map(|_| rng.gen_range(0..5)).collect::<Vec<u64>>();
            let wm = WaveletMatrix::from(v.clone());
            eprintln!("v: {v:?}");
            for _ in 0..R {
                let l = rng.gen_range(0..n);
                let r = rng.gen_range(l + 1..=n);
                let x = rng.gen_range(0..5);
                eprintln!("l: {l}, r: {r}, x: {x}");
                assert_eq!(
                    wm.countk(x, l..r),
                    v[l..r].iter().filter(|&&v| v == x).count()
                );
            }
        }
    }

    #[test]
    fn wavelet_matrix_countk_test() {
        assert_eq!(WaveletMatrix::from(vec![0u64]).countk(0, 0..1), 1);
    }
}
