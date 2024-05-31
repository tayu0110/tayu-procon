use std::{iter::once, ops::Index};

use crate::MathInt;

/// Enumerate prime numbers using a linear sieve.
///
/// The constructor is const fn, so compile-time computation is possible.
///
/// MAX is exclusive. For example, MAX=10, think of it as enumerating the prime numbers "2..10", not "2..=10".
pub struct Sieve<const MAX: usize = 1000010> {
    count: usize,
    primes: [usize; MAX],
}

impl<const MAX: usize> Sieve<MAX> {
    pub const fn new() -> Self {
        let mut primes = [usize::MAX; MAX];
        let mut count = 0;

        let mut i = 2;
        while i < MAX {
            if primes[i] == usize::MAX {
                primes[i] = i;
                primes[count] = i;
                count += 1;
            }

            let mut j = 0;
            while j < count {
                if primes[j] > primes[i] || primes[j] * i >= MAX {
                    break;
                }
                primes[primes[j] * i] = primes[j];
                j += 1;
            }

            i += 1;
        }

        Self { count, primes }
    }

    pub const fn count(&self) -> usize {
        self.count
    }

    pub fn primes(&self) -> impl Iterator<Item = usize> + '_ {
        self.primes.iter().copied().take(self.count)
    }
}

impl Index<usize> for Sieve {
    type Output = usize;
    fn index(&self, index: usize) -> &Self::Output {
        &self.primes[index]
    }
}

/// Memory-saving and compact sieve.
///
/// It does not have information about prime factors, only whether a given natural number is prime or not.
pub struct CompactSieve {
    size: usize,
    block: Vec<u64>,
}

macro_rules! make_mask {
    ( $( $m:literal ),* ) => {
        (0 $( | (1 << $m) )*)
    };
}

impl CompactSieve {
    const B: usize = u64::BITS as usize;
    const B2: usize = Self::B * 2;
    const T: usize = Self::B.trailing_zeros() as usize;
    const T2: usize = Self::T + 1;

    pub fn eratosthenes(size: usize) -> Self {
        let len = (size + Self::B2 - 1) >> Self::T2;
        let mut block = vec![u64::MAX; len];
        let get = |now: usize| (now >> Self::T2, (now >> 1) & (Self::B - 1));
        let mut i = 3;
        while i < size {
            let (b, p) = get(i);
            if block[b] == 0 {
                i += Self::B2;
                continue;
            }

            if (block[b] >> p) & 1 != 0 {
                for (b, p) in (3..)
                    .step_by(2)
                    .map(|j| i * j)
                    .take_while(|&j| j < len << Self::T2)
                    .map(get)
                {
                    block[b] &= !(1 << p);
                }
            }

            i += 2;
        }

        Self { size, block }
    }

    pub fn atkin(size: usize) -> Self {
        let len = (size + Self::B2 - 1) >> Self::T2;
        let mut block = vec![0; len];
        let get = |now: usize| (now >> Self::T2, (now >> 1) & (Self::B - 1));
        let sq = size.sqrti();
        for x in (1..sq + 1).map(|x| 4 * x * x).take_while(|&x| x < size) {
            for n in (1..sq + 1)
                .step_by(2)
                .map(|y| x + y * y)
                .take_while(|&n| n < size)
            {
                const MASK: usize = make_mask!(1, 13, 17, 29, 37, 41, 49, 53);
                if MASK & (1 << (n % 60)) != 0 {
                    let (b, p) = get(n);
                    block[b] ^= 1 << p;
                }
            }
        }
        for x in (1..sq + 1)
            .step_by(2)
            .map(|x| 3 * x * x)
            .take_while(|&x| x < size)
        {
            for n in (2..sq + 1)
                .step_by(2)
                .map(|y| x + y * y)
                .take_while(|&n| n < size)
            {
                const MASK: usize = make_mask!(7, 19, 31, 43);
                if MASK & (1 << (n % 60)) != 0 {
                    let (b, p) = get(n);
                    block[b] ^= 1 << p;
                }
            }
        }
        for x in (2..).take_while(|&x| 2 * x * (x + 1) - 1 < size) {
            for n in (1 + (x & 1)..x)
                .step_by(2)
                .map(|y| 3 * x * x - y * y)
                .skip_while(|&n| n >= size)
            {
                const MASK: usize = make_mask!(11, 23, 47, 59);
                if MASK & (1 << (n % 60)) != 0 {
                    let (b, p) = get(n);
                    block[b] ^= 1 << p;
                }
            }
        }

        const MASK: [usize; 16] = [1, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 49, 53, 59];
        for i in (0..size)
            .step_by(60)
            .flat_map(|i| MASK.into_iter().map(move |j| i + j))
            .skip_while(|&i| i < 7)
            .take_while(|i| i * i < size)
        {
            let (b, p) = get(i);
            if (block[b] >> p) & 1 != 0 {
                let k = i * i;
                for j in (0..)
                    .step_by(60)
                    .flat_map(|i| MASK.into_iter().map(move |j| (i + j) * k))
                    .take_while(|&j| j < size)
                {
                    let (b, p) = get(j);
                    block[b] &= !(1 << p);
                }
            }
        }

        block[0] |= 7;
        Self { size, block }
    }

    /// Construct a sieve in the range `0..size`.
    pub fn new(size: usize) -> Self {
        Self::atkin(size)
    }

    /// Enumerate prime numbers in the range of `0..size`.
    ///
    /// # Examples
    /// ```rust
    /// use math::CompactSieve;
    ///
    /// let sieve = CompactSieve::new(50);
    /// assert_eq!(sieve.primes().collect::<Vec<_>>(), vec![2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]);
    /// ```
    pub fn primes(&self) -> impl Iterator<Item = usize> + '_ {
        once(2)
            .chain(
                self.block
                    .iter()
                    .enumerate()
                    .flat_map(|(i, &b)| {
                        (0..Self::B).filter_map(move |j| {
                            ((b >> j) & 1 != 0).then_some(((j | (i << Self::T)) << 1) | 1)
                        })
                    })
                    .skip(1),
            )
            .take_while(|&p| p < self.size)
    }
}
