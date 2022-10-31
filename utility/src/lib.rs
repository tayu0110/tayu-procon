////////////////////////////////////////////////////////////////////////////////
// Utility
////////////////////////////////////////////////////////////////////////////////

pub trait BinarySearch<T> {
    type Output;
    fn lower_bound(&self, _target: T) -> Option<Self::Output> { unimplemented!() }
    fn upper_bound(&self, _target: T) -> Option<Self::Output> { unimplemented!() }
    /// Return the following 'l'. (If need the following 'r', use upper_bound_by().)  
    ///     L <------  f()=true  ------> lr <------  f()=false  ------> R
    fn lower_bound_by(&self, _f: impl Fn(&T) -> bool) -> Option<Self::Output> { unimplemented!() }
    /// Return the following 'r'. (If need the following 'l', use lower_bound_by().)  
    ///     L <------  f()=true  ------> lr <------  f()=false  ------> R
    fn upper_bound_by(&self, _f: impl Fn(&T) -> bool) -> Option<Self::Output> { unimplemented!() }
}

impl<T: Clone + PartialEq + PartialOrd> BinarySearch<T> for [T] {
    type Output = usize;
    fn lower_bound(&self, target: T) -> Option<Self::Output> {
        let (mut l, mut r) = (-1i32, self.len() as i32);
        while r - l > 1 {
            let m = (r + l) / 2;
            if self[m as usize] < target {
                l = m;
            } else {
                r = m;
            }
        }
        if r == self.len() as i32 {
            None
        } else {
            Some(r as usize)
        }
    }
    fn upper_bound(&self, target: T) -> Option<Self::Output> {
        let (mut l, mut r) = (-1i32, self.len() as i32);
        while r - l > 1 {
            let m = (r + l) / 2;
            if self[m as usize] <= target {
                l = m;
            } else {
                r = m;
            }
        }
        if r == self.len() as i32 {
            None
        } else {
            Some(r as usize)
        }
    }
    fn lower_bound_by(&self, f: impl Fn(&T) -> bool) -> Option<Self::Output> {
        let (mut l, mut r) = (-1i32, self.len() as i32);
        while r - l > 1 {
            let m = (r + l) / 2;
            if f(&self[m as usize]) {
                l = m;
            } else {
                r = m;
            }
        }
        if l == -1 {
            None
        } else {
            Some(l as usize)
        }
    }
    fn upper_bound_by(&self, f: impl Fn(&T) -> bool) -> Option<Self::Output> {
        let (mut l, mut r) = (-1i32, self.len() as i32);
        while r - l > 1 {
            let m = (r + l) / 2;
            if f(&self[m as usize]) {
                l = m;
            } else {
                r = m;
            }
        }
        if r == self.len() as i32 {
            None
        } else {
            Some(r as usize)
        }
    }
}
