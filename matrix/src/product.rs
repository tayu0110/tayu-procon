pub mod dot {
    use super::super::Matrix;
    use modint_common::Modulo;
    use montgomery_modint::{MontgomeryModint, MontgomeryModintx8};
    use static_modint::StaticModint;

    pub trait DotProduct<Rhs = Self> {
        type Output;
        fn dot(self, rhs: Rhs) -> Self::Output;
    }

    pub trait DotProductAssign<Rhs = Self> {
        fn dot_assign(&mut self, rhs: Rhs);
    }

    impl<M: Modulo> DotProduct<Matrix<StaticModint<M>>> for Matrix<StaticModint<M>> {
        type Output = Self;
        fn dot(self, rhs: Matrix<StaticModint<M>>) -> Self::Output {
            type Modint<M> = StaticModint<M>;
            debug_assert!(self.shape().1 == rhs.shape().0);
            let (lrow, lcol) = self.shape();
            let (_, rcol) = rhs.shape();
            let mut data = vec![Modint::zero(); lrow * rcol];
            let rhs = rhs.transpose();
            for (s, t) in data
                .chunks_exact_mut(rcol)
                .zip(self.data.chunks_exact(lcol))
            {
                s.iter_mut()
                    .zip(rhs.data.chunks_exact(lcol))
                    .for_each(|(x, u)| {
                        *x = t
                            .iter()
                            .zip(u.iter())
                            .fold(Modint::zero(), |s, (&v, &w)| s + v * w)
                    });
            }
            Matrix { row: lrow as u32, col: rcol as u32, data }
        }
    }

    #[target_feature(enable = "avx")]
    #[target_feature(enable = "avx2")]
    unsafe fn naive_algorithm<M: Modulo>(
        mut a: Matrix<MontgomeryModint<M>>,
        mut b: Matrix<MontgomeryModint<M>>,
    ) -> Matrix<MontgomeryModint<M>> {
        type Modint<M> = MontgomeryModint<M>;
        type Modintx8<M> = MontgomeryModintx8<M>;
        const BLOCK_WIDTH: usize = 8;
        const BLOCK_HEIGHT: usize = 8;
        let (lrow, lcol) = a.shape();
        let (_, rcol) = b.shape();
        // Align the width with multiples of 8 to reduce branching inside the loop.
        // According to the profile results, the cost of matrix transposition is miniscule compared to the cost of the main loop, so it is not a problem.
        let width = (lcol + 7) & !7usize;
        assert!(width <= 128);
        if width != lcol {
            a = {
                let mut a = a.transpose();
                a.resize(width, lrow, MontgomeryModint::zero());
                a.transpose()
            };
            b.resize(width, rcol, MontgomeryModint::zero());
        }
        b = b.transpose();

        let mut data = vec![Modint::zero(); lrow * rcol];
        let mut buf = [Modint::zero(); 8];
        for row_base in (0..lrow).step_by(BLOCK_HEIGHT) {
            for col_base in (0..rcol).step_by(BLOCK_WIDTH) {
                for (row, t) in a.data[row_base * width..]
                    .chunks_exact(width)
                    .enumerate()
                    .take(BLOCK_HEIGHT)
                    .map(|(i, t)| (i + row_base, t))
                {
                    for (col, u) in b.data[col_base * width..]
                        .chunks_exact(width)
                        .enumerate()
                        .take(BLOCK_WIDTH)
                        .map(|(i, u)| (i + col_base, u))
                    {
                        let res = t
                            .chunks_exact(8)
                            .zip(u.chunks_exact(8))
                            .fold(Modintx8::zero(), |s, (v, w)| {
                                s + Modintx8::load(v.as_ptr()) * Modintx8::load(w.as_ptr())
                            });
                        res.store(buf.as_mut_ptr());
                        data[row * rcol + col] = buf.into_iter().fold(Modint::zero(), |s, v| s + v);
                    }
                }
            }
        }
        Matrix { row: lrow as u32, col: rcol as u32, data }
    }

    fn strassens_algorithm<M: Modulo>(
        mut a: Matrix<MontgomeryModint<M>>,
        mut b: Matrix<MontgomeryModint<M>>,
    ) -> Matrix<MontgomeryModint<M>> {
        let (lrow, lcol) = a.shape();
        let (rrow, rcol) = b.shape();
        let n = lrow.max(lcol).max(rrow).max(rcol).next_power_of_two();
        if n <= 128 {
            return unsafe { naive_algorithm(a, b) };
        }
        a.resize(n, n, MontgomeryModint::zero());
        b.resize(n, n, MontgomeryModint::zero());

        let ((a11, a12), (a21, a22)) = {
            let (a1, a2) = a.split_at_row(n >> 1);
            (a1.split_at_col(n >> 1), a2.split_at_col(n >> 1))
        };
        let ((b11, b12), (b21, b22)) = {
            let (b1, b2) = b.split_at_row(n >> 1);
            (b1.split_at_col(n >> 1), b2.split_at_col(n >> 1))
        };

        let p1 = strassens_algorithm(a11.clone() + a22.clone(), b11.clone() + b22.clone());
        let p2 = strassens_algorithm(a21.clone() + a22.clone(), b11.clone());
        let p3 = strassens_algorithm(a11.clone(), b12.clone() - b22.clone());
        let p4 = strassens_algorithm(a22.clone(), b21.clone() - b11.clone());
        let p5 = strassens_algorithm(a11.clone() + a12.clone(), b22.clone());
        let p6 = strassens_algorithm(a21 - a11, b11 + b12);
        let p7 = strassens_algorithm(a12 - a22, b21 + b22);

        let c11 = p1.clone() + p4.clone() - p5.clone() + p7;
        let c12 = p3.clone() + p5;
        let c21 = p2.clone() + p4;
        let c22 = p1 + p3 - p2 + p6;
        let c1 = Matrix::merge_horizontal(c11, c12);
        let c2 = Matrix::merge_horizontal(c21, c22);
        let mut c = Matrix::merge_vertical(c1, c2);
        c.resize(lrow, rcol, MontgomeryModint::zero());
        c
    }

    impl<M: Modulo> DotProduct<Matrix<MontgomeryModint<M>>> for Matrix<MontgomeryModint<M>> {
        type Output = Self;
        fn dot(self, rhs: Matrix<MontgomeryModint<M>>) -> Self::Output {
            debug_assert!(self.shape().1 == rhs.shape().0);
            strassens_algorithm(self, rhs)
        }
    }
}

pub mod frobenius {
    pub trait FrobeniusProduct<Rhs = Self> {
        type Output;
        fn frobenius(self, rhs: Rhs) -> Self::Output;
    }
}

pub mod hadamard {
    pub trait HadamardProduct<Rhs = Self> {
        type Output;
        fn hadamard(self, rhs: Rhs) -> Self::Output;
    }

    pub trait HadamardProductAssign<Rhs = Self> {
        fn hadamard_assign(&mut self, rhs: Rhs);
    }
}

pub mod scalar {
    pub trait ScalarProduct<Rhs> {
        type Output;
        fn scalar_product(self, rhs: Rhs) -> Self::Output;
    }

    pub trait ScalarProductAssign<Rhs> {
        fn scalar_product_assign(&mut self, rhs: Rhs);
    }
}
