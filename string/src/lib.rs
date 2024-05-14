mod palindrome;
mod rolling_hash;
mod suffix_array;

use std::ops::Range;

pub use palindrome::*;
pub use rolling_hash::*;
pub use suffix_array::*;

/// For given string S, return an array that records as the i-th element the longest common prefix of S and the substring starting from the i-th element of S.
// https://atcoder.jp/contests/abc135/submissions/34695512
pub fn zalgorithm(s: impl Into<String>) -> Vec<usize> {
    let s: String = s.into();
    let mut z = vec![0; s.len()];
    z[0] = s.len();

    let (mut i, mut j) = (1, 0);
    while i < s.len() {
        while i + j < s.len() && s[j..j + 1] == s[i + j..i + j + 1] {
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

/// Returns all `Range`s of the longest common substring of `s` and `t`.  
/// The first element of the tuple is the range in `s` and the next element is the range in `t`.
pub fn longest_common_substring<'a>(
    s: &'a str,
    t: &'a str,
) -> impl Iterator<Item = (Range<usize>, Range<usize>)> + 'a {
    let u = [s, " ", t].concat();
    let sa = SuffixArray::new(&u);
    let lcpa = sa.lcp_array();
    let sa = sa.into_iter().collect::<Vec<_>>();

    let mut max = 0;
    for (i, &lcp) in lcpa.iter().enumerate() {
        let a = sa[i] as usize;
        let b = sa[i + 1] as usize;
        let (a, b) = (a.min(b), a.max(b));
        if a < s.len() && s.len() < b {
            max = max.max(lcp.min(s.len() - a));
        }
    }

    let mut i = 0;
    std::iter::from_fn(move || {
        if max == 0 {
            return None;
        }

        while i < lcpa.len() {
            let a = sa[i] as usize;
            let b = sa[i + 1] as usize;
            let (a, b) = (a.min(b), a.max(b));
            if a < s.len() && s.len() < b && lcpa[i] == max {
                let b = b - s.len() - 1;
                return Some((a..a + max, b..b + max));
            }

            i += 1;
        }

        None
    })
}
