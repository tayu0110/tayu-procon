mod rolling_hash;

pub use rolling_hash::*;

////////////////////////////////////////////////////////////////////////////////
// String Utility
////////////////////////////////////////////////////////////////////////////////

pub trait IntoVec<T> {
    fn into_vec(&self) -> Vec<T>;
}

impl IntoVec<char> for String {
    fn into_vec(&self) -> Vec<char> { self.chars().collect() }
}

impl IntoVec<u8> for String {
    fn into_vec(&self) -> Vec<u8> { self.bytes().collect() }
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
        while i + j < s.len() && &s[j..j + 1] == &s[i + j..i + j + 1] {
            j += 1;
        }
        z[i] = j;

        if j == 0 {
            i += 1;
            continue;
        }

        let mut k = 1;
        while i + k < s.len() && k + z[k] < j {
            z[i + k] = z[k];
            k += 1;
        }

        i += k;
        j -= k;
    }

    z
}
