use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign};

pub const BIT_SIZE: usize = std::mem::size_of::<u128>();
pub const LOG: u32 = BIT_SIZE.count_zeros();
struct Bitset {
    size: usize,
    bits: Vec<u128>,
}

impl Bitset {
    pub fn new(size: usize) -> Self {
        Self {
            size,
            bits: vec![0; (size + BIT_SIZE - 1) >> LOG],
        }
    }

    pub const fn size(&self) -> usize { self.size }

    pub fn set(&mut self, idx: usize) {
        debug_assert!(idx < self.size);

        let (idx, bit) = (idx >> LOG, idx & (BIT_SIZE - 1));
        self.bits[idx] |= 1 << bit;
    }

    pub fn drop(&mut self, idx: usize) {
        debug_assert!(idx < self.size);

        let (idx, bit) = (idx >> LOG, idx & (BIT_SIZE - 1));
        self.bits[idx] ^= 1 << bit;
    }

    pub fn flip(&mut self) {
        self.bits.iter_mut().for_each(|v| *v = !*v);

        if self.size & (BIT_SIZE - 1) != 0 {
            let sz = self.size & (BIT_SIZE - 1);
            *self.bits.last_mut().unwrap() &= (1 << (sz + 1)) - 1;
        }
    }

    pub fn test(&self, idx: usize) -> bool { (self.bits[idx >> LOG] & (1u128 << (idx & (BIT_SIZE - 1)))) != 0 }

    pub fn count_ones(&self) -> usize { self.bits.iter().map(|v| v.count_ones() as usize).sum() }

    pub fn count_zeros(&self) -> usize { self.size - self.count_ones() }

    pub fn bitwise_and(&self, rhs: &Bitset) -> Self {
        let bits = self.bits.iter().zip(rhs.bits.iter()).fold(Vec::with_capacity(self.size), |mut s, (v, w)| {
            s.push(v & w);
            s
        });
        Self { size: self.size, bits }
    }

    pub fn bitwise_or(&self, rhs: &Bitset) -> Bitset {
        let bits = self.bits.iter().zip(rhs.bits.iter()).fold(Vec::with_capacity(self.size), |mut s, (v, w)| {
            s.push(v | w);
            s
        });
        Self { size: self.size, bits }
    }

    pub fn bitwise_xor(&self, rhs: &Bitset) -> Self {
        let bits = self.bits.iter().zip(rhs.bits.iter()).fold(Vec::with_capacity(self.size), |mut s, (v, w)| {
            s.push(v ^ w);
            s
        });
        Self { size: self.size, bits }
    }
}

impl BitAnd for Bitset {
    type Output = Bitset;
    fn bitand(self, rhs: Self) -> Self::Output { self.bitwise_and(&rhs) }
}

impl BitOr for Bitset {
    type Output = Bitset;
    fn bitor(self, rhs: Self) -> Self::Output { self.bitwise_or(&rhs) }
}

impl BitXor for Bitset {
    type Output = Bitset;
    fn bitxor(self, rhs: Self) -> Self::Output { self.bitwise_xor(&rhs) }
}

impl BitAndAssign for Bitset {
    fn bitand_assign(&mut self, rhs: Self) { *self = self.bitwise_and(&rhs) }
}

impl BitOrAssign for Bitset {
    fn bitor_assign(&mut self, rhs: Self) { *self = self.bitwise_or(&rhs) }
}

impl BitXorAssign for Bitset {
    fn bitxor_assign(&mut self, rhs: Self) { *self = self.bitwise_xor(&rhs) }
}

impl PartialEq for Bitset {
    fn eq(&self, other: &Self) -> bool { self.bits == other.bits }
}

impl Eq for Bitset {}

impl PartialOrd for Bitset {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> { self.bits.partial_cmp(&other.bits) }

    fn lt(&self, other: &Self) -> bool {
        if let Some((v, w)) = self.bits.iter().rev().zip(other.bits.iter().rev()).skip_while(|(v, w)| v == w).next() {
            v < w
        } else {
            false
        }
    }

    fn le(&self, other: &Self) -> bool {
        if let Some((v, w)) = self.bits.iter().rev().zip(other.bits.iter().rev()).skip_while(|(v, w)| v == w).next() {
            v < w
        } else {
            true
        }
    }

    fn gt(&self, other: &Self) -> bool {
        if let Some((v, w)) = self.bits.iter().rev().zip(other.bits.iter().rev()).skip_while(|(v, w)| v == w).next() {
            v > w
        } else {
            false
        }
    }

    fn ge(&self, other: &Self) -> bool {
        if let Some((v, w)) = self.bits.iter().rev().zip(other.bits.iter().rev()).skip_while(|(v, w)| v == w).next() {
            v > w
        } else {
            true
        }
    }
}

impl Ord for Bitset {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering { self.bits.cmp(&other.bits) }
}

impl std::fmt::Debug for Bitset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result { write!(f, "{:?}", self.bits) }
}
