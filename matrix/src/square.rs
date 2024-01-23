use modint_common::Modulo;
use montgomery_modint::{MontgomeryModint, MontgomeryModintx8};
use zero_one::{One, Zero};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SquareMatrix<T: Clone + Zero> {
    n: usize,
    cap: usize,
    data: Vec<T>,
}

impl<T: Clone + Zero> SquareMatrix<T> {
    fn calc_cap(n: usize) -> usize {
        (n + 7) & !7usize
    }

    pub fn from_vec(data: Vec<Vec<T>>) -> Self {
        let n = data.len();
        assert!(data.iter().all(|v| v.len() == n));
        let data = data.into_iter().flatten().collect();
        Self::from_vec_as_shape(n, data)
    }

    pub fn from_vec_as_shape(n: usize, mut data: Vec<T>) -> Self {
        assert_eq!(n * n, data.len());
        let cap = Self::calc_cap(n);
        if n != cap {
            let mut new = vec![T::zero(); cap * cap];
            new.chunks_exact_mut(cap)
                .zip(data.chunks_exact(n))
                .for_each(|(to, from)| to[..n].clone_from_slice(from));
            data = new;
        }
        Self { n, cap, data }
    }

    pub fn shape(&self) -> usize {
        self.n
    }

    pub fn get(&self, row: usize, col: usize) -> &T {
        debug_assert!(row < self.n && col < self.n);
        &self.data[row * self.cap + col]
    }

    pub fn get_mut(&mut self, row: usize, col: usize) -> &mut T {
        debug_assert!(row < self.n && col < self.n);
        &mut self.data[row * self.cap + col]
    }

    pub fn set(&mut self, row: usize, col: usize, val: T) {
        debug_assert!(row < self.n && col < self.n);
        self.data[row * self.cap + col] = val;
    }
}

impl<T: Clone + Zero + One> SquareMatrix<T> {
    pub fn id(n: usize) -> Self {
        let cap = Self::calc_cap(n);
        let mut data = vec![T::zero(); cap * cap];
        for i in 0..n {
            data[i * cap + i] = T::one();
        }
        Self { n, cap, data }
    }
}

impl<M: Modulo> SquareMatrix<MontgomeryModint<M>> {
    pub fn transpose(&self) -> Self {
        type Modint<M> = MontgomeryModint<M>;
        type Modintx8<M> = MontgomeryModintx8<M>;

        if self.n == 1 {
            return self.clone();
        }

        if self.n < 8 {
            let mut res = self.clone();
            for i in 0..self.n {
                for j in i + 1..self.n {
                    res.data.swap(i * self.n + j, j * self.n + i);
                }
            }
            return res;
        }

        let mut new = vec![Modint::zero(); self.cap * self.cap];
        const BLOCK: usize = 8;
        unsafe {
            for i in (0..self.cap).step_by(BLOCK) {
                for j in (0..self.cap).step_by(BLOCK) {
                    let p = self.data[i * self.cap + j..].as_ptr();
                    let a0 = Modintx8::load(p);
                    let a1 = Modintx8::load(p.add(self.cap));
                    let a2 = Modintx8::load(p.add(self.cap * 2));
                    let a3 = Modintx8::load(p.add(self.cap * 3));
                    let a4 = Modintx8::load(p.add(self.cap * 4));
                    let a5 = Modintx8::load(p.add(self.cap * 5));
                    let a6 = Modintx8::load(p.add(self.cap * 6));
                    let a7 = Modintx8::load(p.add(self.cap * 7));

                    let b0 = a0.unpacklo32(a1);
                    let b1 = a0.unpackhi32(a1);
                    let b2 = a2.unpacklo32(a3);
                    let b3 = a2.unpackhi32(a3);
                    let b4 = a4.unpacklo32(a5);
                    let b5 = a4.unpackhi32(a5);
                    let b6 = a6.unpacklo32(a7);
                    let b7 = a6.unpackhi32(a7);

                    let c0 = b0.unpacklo64(b2);
                    let c1 = b0.unpackhi64(b2);
                    let c2 = b1.unpacklo64(b3);
                    let c3 = b1.unpackhi64(b3);
                    let c4 = b4.unpacklo64(b6);
                    let c5 = b4.unpackhi64(b6);
                    let c6 = b5.unpacklo64(b7);
                    let c7 = b5.unpackhi64(b7);

                    let p = new[i * self.cap + j..].as_mut_ptr();
                    c0.permute2x128::<0x20>(c4).store(p);
                    c1.permute2x128::<0x20>(c5).store(p.add(self.cap));
                    c2.permute2x128::<0x20>(c6).store(p.add(self.cap * 2));
                    c3.permute2x128::<0x20>(c7).store(p.add(self.cap * 3));
                    c0.permute2x128::<0x31>(c4).store(p.add(self.cap * 4));
                    c1.permute2x128::<0x31>(c5).store(p.add(self.cap * 5));
                    c2.permute2x128::<0x31>(c6).store(p.add(self.cap * 6));
                    c3.permute2x128::<0x31>(c7).store(p.add(self.cap * 7));
                }
            }
        }

        Self { n: self.n, cap: self.cap, data: new }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use modint_common::Mod998244353;

    type Modint = MontgomeryModint<Mod998244353>;

    #[test]
    fn transpose_test() {
        let data = (0..64).map(Modint::new).collect();
        let mat = SquareMatrix::from_vec_as_shape(8, data);

        let transposed = mat.transpose();
        #[rustfmt::skip]
        let expected: SquareMatrix<Modint> = SquareMatrix::from_vec(vec![
            vec![0.into(), 8.into(), 16.into(), 24.into(), 32.into(), 40.into(), 48.into(), 56.into()],
            vec![1.into(), 9.into(), 17.into(), 25.into(), 33.into(), 41.into(), 49.into(), 57.into()],
            vec![2.into(), 10.into(), 18.into(), 26.into(), 34.into(), 42.into(), 50.into(), 58.into()],
            vec![3.into(), 11.into(), 19.into(), 27.into(), 35.into(), 43.into(), 51.into(), 59.into()],
            vec![4.into(), 12.into(), 20.into(), 28.into(), 36.into(), 44.into(), 52.into(), 60.into()],
            vec![5.into(), 13.into(), 21.into(), 29.into(), 37.into(), 45.into(), 53.into(), 61.into()],
            vec![6.into(), 14.into(), 22.into(), 30.into(), 38.into(), 46.into(), 54.into(), 62.into()],
            vec![7.into(), 15.into(), 23.into(), 31.into(), 39.into(), 47.into(), 55.into(), 63.into()],
        ]);
        assert_eq!(transposed, expected);
    }
}
