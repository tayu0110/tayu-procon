use std::{collections::BTreeMap, fmt::Debug, ops::RangeBounds};

pub struct BTreeMultiSet<K> {
    len: usize,
    inner: BTreeMap<K, u32>,
}

impl<'a, K: Ord + Debug + Clone> BTreeMultiSet<K> {
    #[inline]
    pub fn new() -> Self {
        Self { len: 0, inner: BTreeMap::new() }
    }
    #[inline]
    pub fn insert(&mut self, key: K) {
        *self.inner.entry(key).or_insert(0) += 1;
        self.len += 1;
    }
    #[inline]
    pub fn remove(&mut self, key: &K) {
        if !self.inner.contains_key(key) {
            return;
        }

        self.len -= 1;
        if *self.inner.get(key).unwrap() == 1 {
            self.inner.remove(key);
        } else {
            *self.inner.get_mut(key).unwrap() -= 1;
        }
    }
    #[inline]
    pub fn remove_all(&mut self, key: &K) {
        self.len -= *self.inner.get(key).unwrap_or(&0) as usize;
        self.inner.remove(key);
    }
    #[inline]
    pub fn count(&mut self, key: &K) -> usize {
        *self.inner.get(key).unwrap_or(&0) as usize
    }
    #[inline]
    pub fn len(&self) -> usize {
        self.len
    }
    #[inline]
    pub fn clear(&mut self) {
        self.inner.clear();
        self.len = 0;
    }
    #[inline]
    pub fn has_duplicate(&self) -> bool {
        self.len() != self.inner.len()
    }
    #[inline]
    pub fn contains(&self, key: &K) -> bool {
        self.inner.contains_key(key)
    }
    #[inline]
    pub fn first(&self) -> Option<&K> {
        self.inner.iter().next().map(|(k, _)| k)
    }
    #[inline]
    pub fn get(&self, key: &K) -> Option<&K> {
        self.inner.get_key_value(key).map(|(k, _)| k)
    }
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }
    #[inline]
    pub fn last(&self) -> Option<&K> {
        self.inner.iter().next_back().map(|(k, _)| k)
    }
    /// Generate an iterator of `self`
    ///
    /// # Examples
    /// ```rust
    /// use ds::BTreeMultiSet;
    ///
    /// let mut st = BTreeMultiSet::new();
    /// st.insert(0);
    /// st.insert(1);
    /// st.insert(1);
    /// st.insert(2);
    /// let v = st.iter().copied().collect::<Vec<_>>();
    /// assert_eq!(v, vec![0, 1, 1, 2]);
    /// ```
    #[inline]
    pub fn iter(&'a self) -> impl DoubleEndedIterator<Item = &'a K> + 'a {
        self.inner
            .iter()
            .flat_map(|(k, &cnt)| (0..cnt).map(move |_| k))
    }
    #[inline]
    pub fn range<R: RangeBounds<K>>(
        &'a self,
        range: R,
    ) -> impl DoubleEndedIterator<Item = &'a K> + 'a {
        self.inner
            .range(range)
            .flat_map(|(k, &cnt)| (0..cnt).map(move |_| k))
    }
}

impl<K: Ord + Debug + Clone> Default for BTreeMultiSet<K> {
    fn default() -> Self {
        Self::new()
    }
}
