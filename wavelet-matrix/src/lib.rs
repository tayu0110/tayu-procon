#![allow(clippy::ptr_arg)]

#[derive(Clone, Debug)]
struct BitVector {
    size: u32,
    zeros: u32,
    block: Vec<u64>,
    count: Vec<u32>,
}

impl BitVector {
    const WORD: usize = 64;
    const LOG: u32 = Self::WORD.trailing_zeros();
    const MASK: usize = Self::WORD - 1;

    #[inline]
    fn new(size: usize) -> Self {
        let (size, zeros) = (size as u32, size as u32);
        let block = vec![0; (size >> Self::LOG) as usize + 1];
        let count = vec![0; block.len()];

        Self { size, zeros, block, count }
    }

    #[inline]
    fn access(&self, idx: usize) -> u32 {
        (self.block[idx >> Self::LOG] >> (idx & Self::MASK)) as u32 & 1
    }

    #[inline]
    fn set(&mut self, idx: usize) {
        self.block[idx >> Self::LOG] |= 1u64 << (idx & Self::MASK)
    }

    #[inline]
    /// return the number of '0' in [0, idx)
    fn rank0(&self, idx: usize) -> u32 {
        idx as u32 - self.rank1(idx)
    }

    #[inline]
    /// return the number of '1' in [0, idx)
    fn rank1(&self, idx: usize) -> u32 {
        self.count[idx >> Self::LOG]
            + (self.block[idx >> Self::LOG] & ((1 << (idx & Self::MASK)) - 1)).count_ones()
    }

    #[inline]
    // return the index of n-th '0' (0-based)
    fn select0(&self, n: usize) -> usize {
        let (mut l, mut r) = (0, self.size as usize);
        while r - l > 1 {
            let m = (r + l) / 2;
            let rank0 = self.rank0(m) as usize;
            if rank0 < n + 1 {
                l = m;
            } else {
                r = m;
            }
        }
        r
    }

    #[inline]
    // return the index of n-th '1' (0-based)
    fn select1(&self, n: usize) -> usize {
        let (mut l, mut r) = (0, self.size as usize);
        while r - l > 1 {
            let m = (r + l) / 2;
            let rank1 = self.rank1(m) as usize;
            if rank1 < n + 1 {
                l = m;
            } else {
                r = m;
            }
        }
        r
    }

    fn build(&mut self) {
        self.count = (0..=0)
            .chain(self.block.iter().cloned())
            .scan(0, |s, v| {
                *s += v.count_ones();
                Some(*s)
            })
            .collect::<Vec<_>>();

        self.zeros = self.rank0(self.size as usize);
    }
}

#[derive(Clone, Debug)]
pub struct WaveletMatrix {
    log: usize,
    bit_vector: Vec<BitVector>,
    first_index: std::collections::HashMap<i64, usize>,
}

impl WaveletMatrix {
    #[inline]
    pub fn from_vec(a: &Vec<i64>) -> Self {
        let (log, bit_vector, first_index) = Self::build(a.len(), a);
        Self { log, bit_vector, first_index }
    }

    fn build(
        size: usize,
        a: &Vec<i64>,
    ) -> (usize, Vec<BitVector>, std::collections::HashMap<i64, usize>) {
        let log = (std::cmp::max(*a.iter().max().unwrap_or(&0), 1) as u64 + 1)
            .next_power_of_two()
            .trailing_zeros() as usize;
        let mut bit_vector = vec![BitVector::new(size); log];
        let mut now = a.clone();
        let mut next = vec![0; size];
        for (h, bv) in bit_vector.iter_mut().enumerate().rev() {
            (0..size)
                .filter(|&i| (now[i] >> h) & 1 != 0)
                .for_each(|i| bv.set(i));
            bv.build();
            let mut idx = [0, bv.zeros as usize];
            for (i, j) in (0..size).map(|i| (i, bv.access(i) as usize)) {
                next[idx[j]] = now[i];
                idx[j] += 1;
            }
            std::mem::swap(&mut now, &mut next);
        }

        let mut prev = std::i64::MIN;
        let mut first_index = std::collections::HashMap::new();
        for (i, v) in now.into_iter().enumerate() {
            if prev != v {
                first_index.insert(v, i);
                prev = v;
            }
        }

        (log, bit_vector, first_index)
    }

    #[inline]
    fn succ0(&self, l: usize, r: usize, bv: &BitVector) -> (u32, u32) {
        (bv.rank0(l), bv.rank0(r))
    }

    #[inline]
    fn succ1(&self, l: usize, r: usize, bv: &BitVector) -> (u32, u32) {
        let (l0, r0) = self.succ0(l, r, bv);
        (l as u32 + bv.zeros - l0, r as u32 + bv.zeros - r0)
    }

    pub fn access(&self, mut idx: usize) -> i64 {
        let mut res = 0;
        for (h, bv) in self.bit_vector.iter().enumerate().rev() {
            let f = bv.access(idx);
            res |= if f != 0 { 1 << h } else { 0 };
            idx = if f != 0 { bv.rank1(idx) + bv.zeros } else { bv.rank0(idx) } as usize;
        }
        res
    }

    /// return the number of k included in [0, r).
    pub fn rank(&self, mut r: usize, k: i64) -> usize {
        if let Some(nk) = self.first_index.get(&k) {
            for (h, bv) in self.bit_vector.iter().enumerate().rev() {
                let bit = (k >> h) & 1;
                r = if bit == 0 { bv.rank0(r) } else { bv.rank1(r) + bv.zeros } as usize;
            }
            r - *nk
        } else {
            0
        }
    }

    pub fn select(&self, idx: usize, k: i64) -> Option<usize> {
        let size = self.bit_vector[0].size;

        if idx >= self.rank(size as usize, k) || !self.first_index.contains_key(&k) {
            return None;
        }

        let mut i = *self.first_index.get(&k).unwrap() + idx;
        for (h, bv) in self.bit_vector.iter().enumerate() {
            let bit = (k >> h) & 1;
            i = if bit == 0 { bv.select0(i) } else { bv.select1(i - bv.zeros as usize) } - 1;
        }

        Some(i)
    }

    pub fn kth_smallest(&self, mut l: usize, mut r: usize, mut k: usize) -> i64 {
        let mut res = 0;
        for (h, bv) in self.bit_vector.iter().enumerate().rev() {
            let (l0, r0) = self.succ0(l, r, bv);
            (l, r) = if (k as u32) < r0 - l0 {
                (l0 as usize, r0 as usize)
            } else {
                k -= (r0 - l0) as usize;
                res |= 1 << h;
                let (l1, r1) = self.succ1(l, r, bv);
                (l1 as usize, r1 as usize)
            }
        }
        res
    }

    #[inline]
    pub fn kth_largest(&self, l: usize, r: usize, k: usize) -> i64 {
        self.kth_smallest(l, r, r - l - k - 1)
    }

    fn range_freq_inner(&self, mut l: usize, mut r: usize, upper: i64) -> usize {
        if upper >= 1 << self.log {
            return r - l;
        }
        let mut res = 0;
        for (h, bv) in self.bit_vector.iter().enumerate().rev() {
            let f = (upper >> h) & 1;
            let (l0, r0) = self.succ0(l, r, bv);
            (l, r) = if f != 0 {
                res += (r0 - l0) as usize;
                let (l1, r1) = self.succ1(l, r, bv);
                (l1 as usize, r1 as usize)
            } else {
                (l0 as usize, r0 as usize)
            }
        }
        res
    }

    #[inline]
    pub fn range_freq(&self, l: usize, r: usize, lower: i64, upper: i64) -> usize {
        self.range_freq_inner(l, r, upper) - self.range_freq_inner(l, r, lower)
    }

    #[inline]
    pub fn prev_value(&self, l: usize, r: usize, upper: i64) -> i64 {
        let cnt = self.range_freq_inner(l, r, upper);
        if cnt == 0 {
            -1
        } else {
            self.kth_smallest(l, r, cnt - 1)
        }
    }

    #[inline]
    pub fn next_value(&self, l: usize, r: usize, lower: i64) -> i64 {
        let cnt = self.range_freq_inner(l, r, lower);
        if cnt == r - l {
            -1
        } else {
            self.kth_smallest(l, r, cnt)
        }
    }
}

#[cfg(test)]
mod test {
    use super::WaveletMatrix;

    const TEST_ARRAY: [i64; 12] = [5, 4, 5, 5, 2, 1, 5, 6, 1, 3, 5, 0];

    #[test]
    fn rank_test() {
        let v = TEST_ARRAY.to_vec();
        let wm = WaveletMatrix::from_vec(&v);

        assert_eq!(wm.rank(9, 5), 4);
        assert_eq!(wm.rank(5, 5), 3);
        assert_eq!(wm.rank(3, 5), 2);
        assert_eq!(wm.rank(4, 0), 0);
        assert_eq!(wm.rank(12, 0), 1);
    }

    #[test]
    fn select_test() {
        let v = TEST_ARRAY.to_vec();
        let wm = WaveletMatrix::from_vec(&v);

        assert_eq!(wm.select(3, 5), Some(6));
        assert_eq!(wm.select(0, 1), Some(5));
        assert_eq!(wm.select(5, 5), None);
        assert_eq!(wm.select(0, 9), None);
    }
}
