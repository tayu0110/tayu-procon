use std::ops::{Add, Mul, Range, Sub};
use zero_one::Zero;

pub struct CumSum2D<T> {
    h: usize,
    w: usize,
    cum: Box<[T]>,
}

impl<T> CumSum2D<T>
where
    T: Add<Output = T> + Sub<Output = T> + Clone + Copy + Zero,
{
    pub fn new(v: Vec<Vec<T>>) -> Self {
        let h = v.len();
        if h == 0 {
            panic!("v.len() must be larger than 0");
        }
        let w = v[0].len();
        if w == 0 {
            panic!("v[0].len() must be larger than 0");
        }

        let mut cum = vec![T::zero(); (h + 1) * (w + 1)].into_boxed_slice();
        cum.chunks_exact_mut(w + 1)
            .skip(1)
            .zip(v)
            .for_each(|(c, v)| c[1..].copy_from_slice(&v[..]));

        for i in 0..h + 1 {
            for j in 0..w {
                cum[i * (w + 1) + j + 1] = cum[i * (w + 1) + j + 1] + cum[i * (w + 1) + j];
            }
        }
        for j in 0..w + 1 {
            for i in 0..h {
                cum[(i + 1) * (w + 1) + j] = cum[(i + 1) * (w + 1) + j] + cum[i * (w + 1) + j];
            }
        }

        Self { h, w, cum }
    }

    fn elem(&self, row: usize, col: usize) -> T {
        self.cum[row * (self.w + 1) + col]
    }

    pub fn sum(&self, row: Range<usize>, col: Range<usize>) -> T {
        let up = row.start;
        let down = row.end;
        let left = col.start;
        let right = col.end;

        if self.h < down || self.w < right {
            panic!(
                "out of index row: {}..{}, col: {}..{}, self.h = {}, self.w = {}",
                up, down, left, right, self.h, self.w
            );
        }

        self.elem(down, right) + self.elem(up, left) - self.elem(down, left) - self.elem(up, right)
    }

    pub fn all_sum(&self) -> T {
        self.cum[(self.h + 1) * (self.w + 1) - 1]
    }
}

impl<T> CumSum2D<T>
where
    T: Add<Output = T> + Sub<Output = T> + Mul<usize, Output = T> + Clone + Copy + Zero,
{
    pub fn sum_as_infinite_grid(&self, row: Range<usize>, col: Range<usize>) -> T {
        let Range { start: up, end: down } = row;
        let Range { start: left, end: right } = col;

        let mut res = self.all_sum() * (down / self.h) * (right / self.w);
        if down % self.h != 0 {
            res = res + self.sum(0..down % self.h, 0..self.w) * (right / self.w);
        }
        if right % self.w != 0 {
            res = res + self.sum(0..self.h, 0..right % self.w) * (down / self.h);
        }
        if down % self.h != 0 && right % self.w != 0 {
            res = res + self.sum(0..down % self.h, 0..right % self.w);
        }

        if up > 0 && left > 0 {
            res = res + self.sum_as_infinite_grid(0..up, 0..left);
        }
        if up > 0 && right > 0 {
            res = res - self.sum_as_infinite_grid(0..up, 0..right);
        }
        if down > 0 && left > 0 {
            res = res - self.sum_as_infinite_grid(0..down, 0..left);
        }

        res
    }

    pub fn sum_as_infinite_grid_isize(&self, row: Range<isize>, col: Range<isize>) -> T {
        let Range { start: up, end: down } = row;
        let Range { start: left, end: right } = col;

        let padr = up.div_euclid(self.h as isize) * self.h as isize;
        let padc = left.div_euclid(self.w as isize) * self.w as isize;

        self.sum_as_infinite_grid(
            (up - padr) as usize..(down - padr) as usize,
            (left - padc) as usize..(right - padc) as usize,
        )
    }
}
