////////////////////////////////////////////////////////////////
// Trie Tree
////////////////////////////////////////////////////////////////

#[derive(Clone)]
struct Node {
    terminal: usize,
    next: Vec<usize>,
}

pub struct Trie {
    node: Vec<Node>,
}

impl Trie {
    /// Generate an empty Trie tree.
    pub fn new() -> Self {
        Self {
            node: vec![Node { terminal: 0, next: vec![std::usize::MAX; 26] }],
        }
    }

    /// Insert a string to Trie tree.
    pub fn insert(&mut self, s: &str) {
        let mut now = 0;

        for c in s.chars() {
            let idx = c as usize - b'a' as usize;

            if self.node[now].next[idx] == std::usize::MAX {
                self.node[now].next[idx] = self.node.len();
                now = self.node.len();
                self.node
                    .push(Node { terminal: 0, next: vec![std::usize::MAX; 26] });
            } else {
                now = self.node[now].next[idx];
            }
        }

        self.node[now].terminal += 1;
    }

    /// Determine if there is a string that is an exact match to the given string.
    pub fn match_exact(&self, s: &str) -> bool {
        let mut now = 0;

        for c in s.chars() {
            let idx = c as usize - b'a' as usize;

            if self.node[now].next[idx] != std::usize::MAX {
                now = self.node[now].next[idx];
            } else {
                return false;
            }
        }

        self.node[now].terminal > 0
    }

    /// Determine if there is strings that prefixes the given string.
    pub fn match_as_prefix(&self, s: &str) -> bool {
        let mut now = 0;

        for c in s.chars() {
            let idx = c as usize - b'a' as usize;

            if self.node[now].next[idx] != std::usize::MAX {
                now = self.node[now].next[idx];
            } else {
                return false;
            }
        }

        true
    }
}

impl Default for Trie {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    #![allow(clippy::unnecessary_to_owned)]
    use crate::Trie;

    #[test]
    fn trie_test() {
        let mut trie = Trie::new();

        trie.insert("atcoder");
        trie.insert(&"codeforces".to_string());

        assert!(trie.match_exact(&"atcoder".to_string()));
        assert!(trie.match_exact("codeforces"));
        assert!(trie.match_as_prefix("codef"));
        assert!(trie.match_as_prefix("atcoder"));

        assert!(!trie.match_exact("codeforceses"));
        assert!(!trie.match_exact("codef"));
    }
}
