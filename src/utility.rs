////////////////////////////////////////////////////////////////////////////////
// Vec utility
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

impl<T: Clone + PartialEq + PartialOrd> BinarySearch<T> for &[T] {
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

impl<T: Clone + PartialEq + PartialOrd> BinarySearch<T> for Vec<T> {
    type Output = usize;
    fn lower_bound(&self, target: T) -> Option<Self::Output> {
        self.as_slice().lower_bound(target)
    }
    fn upper_bound(&self, target: T) -> Option<Self::Output> {
        self.as_slice().upper_bound(target)
    }
    fn lower_bound_by(&self, f: impl Fn(&T) -> bool) -> Option<Self::Output> {
        self.as_slice().lower_bound_by(f)
    }
    fn upper_bound_by(&self, f: impl Fn(&T) -> bool) -> Option<Self::Output> {
        self.as_slice().upper_bound_by(f)
    }
}




////////////////////////////////////////////////////////////////////////////////
// String Utility
////////////////////////////////////////////////////////////////////////////////

pub trait IntoVec<T> {
    fn into_vec(&self) -> Vec<T>;
}

impl IntoVec<char> for String {
    fn into_vec(&self) -> Vec<char> {
        self.chars().collect()
    }
}

impl IntoVec<u8> for String {
    fn into_vec(&self) -> Vec<u8> {
        self.bytes().collect()
    }
}

macro_rules! into_vec_impl {
    ( $t:ty , $( $rest:tt )+ ) => {
        into_vec_impl!($t);
        into_vec_impl!($( $rest )+);
    };
    ( $t:ty ) => {
        impl IntoVec<$t> for String {
            fn into_vec(&self) -> Vec<$t> {
                self.bytes().map(|v| v as $t).collect()
            }
        }
    };
}

into_vec_impl!(u16, u32, u64, u128, usize, i16, i32, i64, i128, isize);

pub trait SubString {
    fn substring(&self, start: usize, len: usize) -> String;
}

impl SubString for String {
    fn substring(&self, start: usize, len: usize) -> String {
        let end = std::cmp::min(self.len(), start + len);

        self[start..end].to_string()
    }
}

impl SubString for &str {
    fn substring(&self, start: usize, len: usize) -> String {
        let end = std::cmp::min(self.len(), start + len);

        self[start..end].to_string()
    }
}

/// For given string S, return an array that records as the i-th element the longest common prefix of S and the substring starting from the i-th element of S.
// https://atcoder.jp/contests/abc135/submissions/34695512
pub fn zalgorithm(s: impl Into<String>) -> Vec<usize> {
    let s: String = s.into();
    let mut z = vec![0; s.len()];
    z[0] = s.len();

    let (mut i, mut j) = (1, 0);
    while i < s.len() {
        while i + j < s.len() && &s[j..j+1] == &s[i+j..i+j+1] {
            j += 1;
        }
        z[i] = j;

        if j == 0 {
            i += 1;
            continue;
        }

        let mut k = 1;
        while i + k < s.len() && k + z[k] < j {
            z[i+k] = z[k];
            k += 1;
        }

        i += k;
        j -= k;
    }

    z
}

// AI: Implement Suffix array, Suffix tree, Rolling Hash ....
