//! This module has not yes tested.  
//! There may be many bugs.

use std::{
    collections::{BinaryHeap, HashMap},
    ops::{Range, RangeBounds},
};

use crate::convert_range;

// Assuming the size of `BitVector` is up to u32::MAX, determine LARGE_WIDTH as (lg N)^2
const LARGE_WIDTH: usize = 1024;
// Assuming the size of `BitVector` is up to u32::MAX, determine LARGE_WIDTH as (1/2)(lg N)
const SMALL_WIDTH: usize = 16;

type BitBlock = u16;

/// Reference : https://miti-7.hatenablog.com/entry/2018/04/15/155638
struct BitVector {
    large: Box<[u32]>,
    small: Box<[u16]>,
    data: Box<[BitBlock]>,
}

impl BitVector {
    fn new(data: Box<[BitBlock]>) -> Self {
        let l = LARGE_WIDTH / BitBlock::BITS as usize;
        let (mut large, mut small) = (
            Vec::with_capacity((data.len() + l - 1) / l),
            Vec::with_capacity(data.len()),
        );
        small.push(0);
        for large_block in data.chunks(LARGE_WIDTH / BitBlock::BITS as usize) {
            large.push(large.last().unwrap_or(&0) + *small.last().unwrap() as u32);
            *small.last_mut().unwrap() = 0;
            for small_block in large_block {
                small.push(small.last().unwrap() + small_block.count_ones() as u16);
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
    fn count<const B: u8>(&self, to: usize) -> usize {
        assert!(B < 2);
        let l = to / LARGE_WIDTH;
        let s = to / SMALL_WIDTH;

        let mut res = self.large[l] as usize + self.small[s] as usize;

        let rem = to - s * SMALL_WIDTH;
        if rem > 0 {
            res += self.data[s].wrapping_shl(rem as u32).count_ones() as usize;
        }

        if B == 1 {
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
            if self.count::<B>(m) < nth {
                l = m;
            } else {
                r = m;
            }
        }
        r
    }
}

/// Reference : https://miti-7.hatenablog.com/entry/2018/04/28/152259
pub struct WaveletMatrix<T> {
    len: usize,
    bitvec: Vec<BitVector>,
    bound: Vec<usize>,
    first: HashMap<T, u32>,
}

impl WaveletMatrix<u64> {
    pub const fn len(&self) -> usize {
        self.len
    }

    pub const fn is_empty(&self) -> bool {
        self.len() == 0
    }

    #[doc(alias = "access")]
    pub fn get(&self, at: usize) -> u64 {
        let mut res = 0;
        let mut now = at;
        for (bitvec, bound) in self.bitvec.iter().zip(self.bound.iter()) {
            let bit = bitvec.access(now) as u64;
            res = (res << 1) | bit;
            if bit == 0 {
                now = bitvec.count::<0>(now);
            } else {
                now = bound + bitvec.count::<1>(now);
            }
        }

        res
    }

    #[doc(alias = "rank")]
    pub fn countk(&self, to: usize, k: u64) -> usize {
        let Some(&start) = self.first.get(&k) else {
            return 0;
        };

        let mut b = self.bitvec.len();
        let mut now = to;
        for (bitvec, bound) in self.bitvec.iter().zip(self.bound.iter()) {
            b -= 1;

            let bit = (k >> b) & 1;
            if bit == 0 {
                now = bitvec.count::<0>(now);
            } else {
                now = bound + bitvec.count::<1>(now);
            }
        }

        now + 1 - start as usize
    }

    #[doc(alias = "select")]
    pub fn position_of_nth_k(&self, nth: usize, mut k: u64) -> Option<usize> {
        let start = *self.first.get(&k)? as usize;
        (nth < self.countk(self.len(), k)).then(|| {
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

    #[doc(alias = "quantile")]
    pub fn nth_smallest(&self, mut nth: usize, range: impl RangeBounds<usize>) -> u64 {
        let Range { mut start, mut end } = convert_range(self.len(), range);

        let mut res = 0;
        for (bitvec, bound) in self.bitvec.iter().zip(self.bound.iter()) {
            let zeros_until_end = bitvec.count::<0>(end);
            let zeros_until_start = bitvec.count::<0>(start);
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
    }

    pub fn top_of_mode(
        &self,
        range: impl RangeBounds<usize>,
    ) -> impl Iterator<Item = (u64, usize)> + '_ {
        let Range { start, end } = convert_range(self.len(), range);

        let mut nt = BinaryHeap::new();
        nt.push((end - start, start, 0, 0));
        std::iter::from_fn(move || {
            while let Some((width, start, value, level)) = nt.pop() {
                if level == self.bitvec.len() {
                    return Some((value, width));
                }

                let end = width + start;
                let bitvec = &self.bitvec[level];
                let zeros_until_end = bitvec.count::<0>(end);
                let zeros_until_start = bitvec.count::<0>(start);
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

    #[doc(alias = "topk")]
    pub fn topk_of_mode(
        &self,
        k: usize,
        range: impl RangeBounds<usize>,
    ) -> impl Iterator<Item = (u64, usize)> + '_ {
        self.top_of_mode(range).take(k)
    }

    pub fn sum(&self, range: impl RangeBounds<usize>) -> u64 {
        self.top_of_mode(range).map(|(v, cnt)| v * cnt as u64).sum()
    }
}

impl From<Vec<u64>> for WaveletMatrix<u64> {
    fn from(mut value: Vec<u64>) -> Self {
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
                first: HashMap::new(),
            };
        }

        let width = u64::BITS - max.leading_zeros();
        let mut bitvec = vec![];
        let mut bound = vec![];
        for r in (0..width).rev() {
            bitvec.push(BitVector::new(
                value
                    .chunks(BitBlock::BITS as usize)
                    .map(|v| v.iter().fold(0, |s, v| (s << 1) | ((v >> r) & 1)) as u16)
                    .collect(),
            ));

            value.sort_by_key(|&v| (v >> r) & 1);
            bound.push(value.partition_point(|&p| (p >> r) & 1 == 0));
        }

        let mut first = HashMap::from([(value[0], 0)]);
        for (i, v) in value
            .windows(2)
            .enumerate()
            .filter_map(|(i, v)| (v[0] != v[1]).then_some((i, v[1])))
        {
            first.insert(v, i as u32);
        }

        Self { len: value.len(), bitvec, bound, first }
    }
}
