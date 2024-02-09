#[derive(Debug, Clone)]
pub struct CartesianTree {
    root: usize,
    par: Vec<u32>,
    left: Vec<u32>,
    right: Vec<u32>,
}

impl CartesianTree {
    pub fn new<T: Ord>(a: Vec<T>) -> Self {
        let len = a.len();
        let mut res = Self {
            root: 0,
            par: vec![u32::MAX; len],
            left: vec![u32::MAX; len],
            right: vec![u32::MAX; len],
        };

        let mut stack = vec![];
        for i in 0..len {
            let mut p = u32::MAX;
            while let Some(last) = stack.pop() {
                if a[last] < a[i] {
                    stack.push(last);
                    stack.push(i);
                    res.par[i] = last as u32;
                    res.right[last] = i as u32;
                    break;
                }
                p = last as u32;
            }

            if stack.is_empty() {
                stack.push(i);
            }
            if p < u32::MAX {
                res.left[i] = p;
                res.par[p as usize] = i as u32;
            }
        }

        res.root = stack[0];

        res
    }

    pub const fn root(&self) -> usize {
        self.root
    }

    pub fn left(&self, index: usize) -> Option<usize> {
        (self.left[index] < u32::MAX).then_some(self.left[index] as usize)
    }

    pub fn right(&self, index: usize) -> Option<usize> {
        (self.right[index] < u32::MAX).then_some(self.right[index] as usize)
    }

    pub fn parent(&self, index: usize) -> Option<usize> {
        (self.par[index] < u32::MAX).then_some(self.par[index] as usize)
    }

    pub fn parlist(&self) -> Vec<Option<usize>> {
        (0..self.par.len()).map(|i| self.parent(i)).collect()
    }
}
