use std::iter::repeat;

pub struct Palindrome {
    s: String,
    length: Vec<u32>,
}

impl Palindrome {
    pub fn new(s: &str) -> Self {
        let ns = s
            .chars()
            .zip(repeat('\0'))
            .flat_map(|(c, dum)| [c, dum])
            .take(s.len() * 2 - 1)
            .collect::<Vec<char>>();

        Self { s: s.to_owned(), length: Self::manacher(&ns) }
    }

    fn manacher(s: &[char]) -> Vec<u32> {
        let len = s.len();
        let mut res = vec![0; len];

        let (mut i, mut j) = (0, 0);
        while i < len {
            while j <= i && i < len - j && s[i - j] == s[i + j] {
                j += 1;
            }

            res[i] = j as u32;
            let mut k = 1;
            while k <= i && i < len - k && j.saturating_sub(res[i - k] as usize) > k {
                res[i + k] = res[i - k];
                k += 1;
            }
            i += k;
            j -= k;
        }

        for res in res
            .iter_mut()
            .enumerate()
            .filter_map(|(i, res)| ((i as u32) & 1 == *res & 1).then_some(res))
        {
            *res -= 1;
        }

        res
    }

    /// ```rust
    /// use string::Palindrome;
    ///
    /// let pal = Palindrome::new("abcbcba");
    /// assert_eq!(pal.enumerate_length().collect::<Vec<_>>(), vec![1, 0, 1, 0, 3, 0, 7, 0, 3, 0, 1, 0, 1]);
    /// ```
    pub fn enumerate_length(&self) -> impl Iterator<Item = usize> + '_ {
        self.length.iter().map(|&l| l as usize)
    }

    /// ```rust
    /// use string::Palindrome;
    ///
    /// let pal = Palindrome::new("abcdcba");
    /// assert_eq!(pal.longest_palindrome(), "abcdcba");
    ///
    /// let pal = Palindrome::new("abcddcba");
    /// assert_eq!(pal.longest_palindrome(), "abcddcba");
    /// ```
    pub fn longest_palindrome(&self) -> &str {
        let max = self.length.iter().copied().max().unwrap();
        let pos = self.length.iter().position(|&r| r == max).unwrap();

        let r = max as usize / 2;
        let p = pos >> 1;

        if pos & 1 == 0 {
            &self.s[p - r..p + r + 1]
        } else {
            &self.s[p + 1 - r..p + r + 1]
        }
    }
}
