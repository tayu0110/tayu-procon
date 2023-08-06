use std::ops::{Index, IndexMut};

#[derive(Debug, Clone)]
pub struct PartialPersistentArray<T: Clone> {
    gen: usize,
    arr: Vec<Vec<(usize, T)>>,
}

impl<T: Clone> PartialPersistentArray<T> {
    pub fn new(size: usize, default: T) -> Self { Self { gen: 0, arr: vec![vec![(0, default)]; size] } }

    pub fn len(&self) -> usize { self.arr.len() }

    pub fn generation(&self) -> usize { self.gen }

    /// Return the element specified by index at specified generation.
    /// If self[index] has (g0, e0), (g1, e1), ... , (gn, en) and there is the element that gi <= generation, return such element.
    /// If index >= self.len() or self[index] is still not initialized, return None.
    pub fn get(&self, generation: usize, index: usize) -> Option<&T> {
        if self.arr.len() <= index {
            return None;
        }
        let (mut l, mut r) = (0, self.arr[index].len());
        while r - l > 1 {
            let m = (r + l) / 2;
            if self.arr[index][m].0 <= generation {
                l = m;
            } else {
                r = m;
            }
        }

        if l == self.arr.len() {
            None
        } else {
            Some(&self.arr[index][l].1)
        }
    }

    /// Return the mutable reference of the element specified by index.
    /// When this method is called, self[index] is cloned and its generation is updated internally.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if self.arr.len() <= index {
            return None;
        }

        if let Some(last) = self.arr[index].last() {
            self.gen += 1;
            let mut new = last.clone();
            new.0 = self.gen;
            self.arr[index].push(new);
            Some(&mut self.arr[index].last_mut().unwrap().1)
        } else {
            None
        }
    }

    pub fn resize(&mut self, size: usize, default: T) {
        self.gen += 1;
        self.arr.resize(size, vec![(self.gen, default)])
    }
}

impl<T: Clone> Index<usize> for PartialPersistentArray<T> {
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output { self.get(self.gen, index).unwrap() }
}

impl<T: Clone> IndexMut<usize> for PartialPersistentArray<T> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output { self.get_mut(index).unwrap() }
}

#[cfg(test)]
mod tests {
    use super::*;
}
