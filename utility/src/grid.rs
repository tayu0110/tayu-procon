#[derive(Debug, Clone)]
pub struct BinaryGrid<const FILL: char = '#', const EMPTY: char = '.'> {
    inner: Vec<Vec<bool>>,
}

impl<const FILL: char, const EMPTY: char> BinaryGrid<FILL, EMPTY> {
    pub fn new(r: usize, c: usize) -> Self {
        Self { inner: vec![vec![false; c]; r] }
    }

    pub fn from_vec(from: Vec<Vec<char>>) -> Result<Self, String> {
        from.iter()
            .flatten()
            .all(|&c| c == FILL || c == EMPTY)
            .then(|| Self {
                inner: from
                    .into_iter()
                    .map(|v| v.into_iter().map(|c| c == FILL).collect())
                    .collect(),
            })
            .ok_or_else(|| {
                "There are the elements which are different from FILL or EMPTY".to_string()
            })
    }

    /// Return the shape of grid as (rows, columns).
    ///
    /// # Example
    /// ```
    /// use utility::BinaryGrid;
    ///
    /// let grid: BinaryGrid = vec![vec![false; 3]; 2].try_into().unwrap();
    /// assert_eq!(grid.shape(), (2, 3));
    ///
    /// let grid: BinaryGrid = Vec::<Vec<bool>>::try_into(vec![]).unwrap();
    /// assert_eq!(grid.shape(), (0, 0));
    ///
    /// let grid: BinaryGrid = Vec::<Vec<bool>>::try_into(vec![vec![]; 4]).unwrap();
    /// assert_eq!(grid.shape(), (4, 0));
    /// ```
    pub fn shape(&self) -> (usize, usize) {
        (self.inner.len(), self.inner.first().map_or(0, |v| v.len()))
    }

    /// When self is as the following,
    ///
    /// |    |    |    |
    /// |----|----|----|
    /// |  0 |  1 |  2 |
    /// |  3 |  4 |  5 |
    /// |  6 |  7 |  8 |
    /// |  9 | 10 | 11 |
    ///  
    /// this method makes self rotate to the following.
    ///
    /// |    |    |    |    |
    /// |----|----|----|----|
    /// |  2 |  5 |  8 | 11 |
    /// |  1 |  4 |  7 | 10 |
    /// |  0 |  3 |  6 |  9 |
    ///
    /// # Example
    /// ```
    /// use utility::BinaryGrid;
    ///
    /// let grid = BinaryGrid::<'#', '.'>::try_from(vec![
    ///         vec![false, true,  false, false],
    ///         vec![true,  true,  true,  false],
    ///         vec![false, false, false, false],
    ///     ]).unwrap();
    ///
    /// let rotated = grid.rotate90();
    /// assert_eq!(
    ///     rotated.as_ref(),
    ///     &vec![
    ///         vec![false, false, false],
    ///         vec![false, true,  false],
    ///         vec![true,  true,  false],
    ///         vec![false, true,  false],
    ///     ],
    /// );
    /// ```
    pub fn rotate90(self) -> Self {
        if self.inner.is_empty() {
            return self;
        }

        let (h, w) = (self.inner.len(), self.inner[0].len());
        let mut res = vec![vec![false; h]; w];
        for (i, v) in self.inner.into_iter().enumerate() {
            for (j, f) in v.into_iter().enumerate() {
                res[w - 1 - j][i] = f;
            }
        }

        Self { inner: res }
    }

    pub fn rotate180(mut self) -> Self {
        self.inner.reverse();
        self.inner.iter_mut().for_each(|v| v.reverse());
        self
    }

    pub fn truncate(mut self) -> Self {
        for _ in 0..2 {
            while !self.inner.is_empty() && self.inner.last().unwrap().iter().all(|&f| !f) {
                self.inner.pop();
            }
            self.inner.reverse();
        }
        if self.inner.is_empty() {
            return self;
        }
        let len = self.inner.len();
        for _ in 0..2 {
            while !self.inner[0].is_empty()
                && (0..len).map(|i| *self.inner[i].last().unwrap()).all(|f| !f)
            {
                self.inner.iter_mut().for_each(|v| {
                    v.pop();
                })
            }
            self.inner.iter_mut().for_each(|v| v.reverse());
        }
        if self.inner[0].is_empty() {
            self.inner.clear();
        }
        self
    }

    /// Enumerate the neighborhood of coordinate (r, c) by the difference of the coordinates given by d.
    ///
    /// # Example
    /// ```
    /// use utility::BinaryGrid;
    ///
    /// const D: [(usize, usize); 4] = [(0, 1), (1, 0), (0, !0), (!0, 0)];
    ///
    /// let grid: BinaryGrid = BinaryGrid::try_from(vec![
    ///         vec![false, true, false],
    ///         vec![true, false, true],
    ///         vec![false, true, false],
    ///     ]).unwrap();
    ///
    /// let mut neighbor = grid.neighbors(1, 1, &D).collect::<Vec<_>>();
    /// neighbor.sort();
    /// assert_eq!(neighbor, vec![(0, 1), (1, 0), (1, 2), (2, 1)]);
    ///
    /// let mut neighbor = grid.neighbors(0, 2, &D).collect::<Vec<_>>();
    /// neighbor.sort();
    /// assert_eq!(neighbor, vec![(0, 1), (1, 2)]);
    /// ```
    pub fn neighbors<'a>(
        &self,
        r: usize,
        c: usize,
        d: &'a [(usize, usize)],
    ) -> impl Iterator<Item = (usize, usize)> + 'a {
        let (h, w) = (self.inner.len(), self.inner.first().map_or(0, |v| v.len()));
        d.iter().cloned().filter_map(move |(dr, dc)| {
            let nr = r.wrapping_add(dr);
            let nc = c.wrapping_add(dc);
            (nr < h && nc < w).then_some((nr, nc))
        })
    }

    /// Merges the `src` fill with the rectangular region where (r, c) of `self` is the upper left corner.
    ///
    /// # Example
    /// ```
    /// use utility::BinaryGrid;
    ///
    /// let mut dest: BinaryGrid = BinaryGrid::try_from(vec![
    ///         vec![false, false, false],
    ///         vec![false, false, false],
    ///         vec![false, false, false],
    ///     ]).unwrap();
    ///
    /// let src: BinaryGrid = BinaryGrid::try_from(vec![
    ///         vec![true, true],
    ///         vec![true, false]
    ///     ]).unwrap();
    ///
    /// dest.merge(0, 0, &src).ok();
    /// dest.merge(1, 1, &src).ok();
    /// assert_eq!(
    ///     dest.as_ref(),
    ///     &vec![
    ///         vec![true, true, false],
    ///         vec![true, true, true],
    ///         vec![false, true, false],
    ///     ]
    /// );
    ///
    /// assert!(dest.merge(2, 2, &src).is_err());
    /// ```
    pub fn merge(&mut self, r: usize, c: usize, src: &Self) -> Result<(), String> {
        if self.is_overflow(r, c, src) {
            return Err(
                "The grid of the merge source extends beyond the merge destination.".to_string(),
            );
        }

        let (rh, rw) = src.shape();
        for i in r..r + rh {
            for j in c..c + rw {
                self.inner[i][j] |= src.inner[i - r][j - c];
            }
        }

        Ok(())
    }

    pub fn is_overflow(&self, r: usize, c: usize, rhs: &Self) -> bool {
        let (rh, rw) = rhs.shape();
        let (h, w) = self.shape();
        r + rh > h || c + rw > w
    }

    /// Returns whether there is any overlap between the rectangular area where (r, c) of self is the upper left and the filling of rhs.
    ///
    /// # Example
    /// ```
    /// use utility::BinaryGrid;
    ///
    /// let l: BinaryGrid = BinaryGrid::try_from(vec![
    ///         vec![true, true, false],
    ///         vec![true, false, false],
    ///         vec![false, false, true],
    ///     ]).unwrap();
    ///
    /// let r: BinaryGrid = BinaryGrid::try_from(vec![
    ///         vec![true, true],
    ///         vec![true, false],
    ///     ]).unwrap();
    ///
    /// assert!(l.is_overlap(0, 1, &r).unwrap());
    /// assert!(!l.is_overlap(1, 1, &r).unwrap());
    /// ```
    pub fn is_overlap(&self, r: usize, c: usize, rhs: &Self) -> Result<bool, String> {
        if self.is_overflow(r, c, rhs) {
            return Err(
                "The grid of the merge source extends beyond the merge destination.".to_string(),
            );
        }

        let (rh, rw) = rhs.shape();
        for i in r..r + rh {
            for j in c..c + rw {
                if self.inner[i][j] && rhs.inner[i - r][j - c] {
                    return Ok(true);
                }
            }
        }

        Ok(false)
    }

    pub fn restore(self) -> Vec<Vec<char>> {
        self.inner
            .into_iter()
            .map(|v| {
                v.into_iter()
                    .map(|f| if f { FILL } else { EMPTY })
                    .collect()
            })
            .collect()
    }
}

impl<const FILL: char, const EMPTY: char> AsRef<Vec<Vec<bool>>> for BinaryGrid<FILL, EMPTY> {
    fn as_ref(&self) -> &Vec<Vec<bool>> {
        &self.inner
    }
}

impl<const FILL: char, const EMPTY: char> TryFrom<Vec<Vec<char>>> for BinaryGrid<FILL, EMPTY> {
    type Error = String;
    fn try_from(value: Vec<Vec<char>>) -> Result<Self, Self::Error> {
        Self::from_vec(value)
    }
}

impl<const FILL: char, const EMPTY: char> From<Vec<Vec<bool>>> for BinaryGrid<FILL, EMPTY> {
    fn from(value: Vec<Vec<bool>>) -> Self {
        Self { inner: value }
    }
}
