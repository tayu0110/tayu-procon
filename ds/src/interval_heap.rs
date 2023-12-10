/// reference: https://natsugiri.hatenablog.com/entry/2016/10/10/035445  
///
/// This structure can be used as Double Ended Priority Queue.
// Odd index   : min-heap
// Even index  : max-heap
// Each nodes have an interval. The interval of the parent node includes them of the child nodes.
#[doc(alias = "DoubleEndedPriorityQueue")]
#[derive(Debug, Clone)]
pub struct IntervalHeap<T> {
    heap: Vec<T>,
}

impl<T> IntervalHeap<T> {
    pub const fn new() -> Self {
        Self { heap: vec![] }
    }

    pub fn len(&self) -> usize {
        self.heap.len()
    }

    pub fn is_empty(&self) -> bool {
        self.heap.is_empty()
    }

    pub fn shrink_to_fit(&mut self) {
        self.heap.shrink_to_fit();
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self { heap: Vec::with_capacity(capacity) }
    }

    pub fn clear(&mut self) {
        self.heap.clear();
    }
}

impl<T: Ord> IntervalHeap<T> {
    fn parent(&self, node: usize) -> Option<usize> {
        (node > 1).then_some((node >> 1).wrapping_sub(1) & !1)
    }

    fn up_heap(&mut self, mut node: usize, root: usize) -> usize {
        if (node | 1) < self.len() && self.heap[node & !1] > self.heap[node | 1] {
            self.heap.swap(node & !1, node | 1);
            node ^= 1;
        }

        let mut par = self.parent(node);
        // min heap
        while par.is_some() && root < node && self.heap[node] < self.heap[par.unwrap()] {
            self.heap.swap(par.unwrap(), node);
            node = par.unwrap();
            par = self.parent(node);
        }
        // max heap
        let mut par = self.parent(node);
        while par.is_some() && root < node && self.heap[par.unwrap() | 1] < self.heap[node] {
            self.heap.swap(par.unwrap() | 1, node);
            node = par.unwrap() | 1;
            par = self.parent(node);
        }

        node
    }

    fn left_child(&self, node: usize) -> Option<usize> {
        let res = node * 2 + 2 - (node & 1);
        (res < self.len()).then_some(res)
    }

    fn right_child(&self, node: usize) -> Option<usize> {
        let res = node * 2 + 4 - (node & 1);
        (res < self.len()).then_some(res)
    }

    fn down_heap(&mut self, mut node: usize) -> usize {
        if node & 1 != 0 {
            // max heap
            while let Some(mut l) = self.left_child(node) {
                if let Some(r) = self.right_child(node) {
                    l = if self.heap[l] > self.heap[r] { l } else { r };
                }
                if self.heap[node] < self.heap[l] {
                    self.heap.swap(node, l);
                    node = l;
                } else {
                    break;
                }
            }
        } else {
            // min heap
            while let Some(mut l) = self.left_child(node) {
                if let Some(r) = self.right_child(node) {
                    l = if self.heap[l] < self.heap[r] { l } else { r };
                }
                if self.heap[node] > self.heap[l] {
                    self.heap.swap(node, l);
                    node = l;
                } else {
                    break;
                }
            }
        }

        node
    }

    pub fn from_vec(from: Vec<T>) -> Self {
        let n = from.len();
        let mut res = Self { heap: from };
        let half = n >> 1;
        for i in (0..half).rev() {
            let (l, r) = (i << 1, (i << 1) | 1);
            if r < n && res.heap[l] > res.heap[r] {
                res.heap.swap(l, r);
            }

            let k = res.down_heap(r);
            res.up_heap(k, r);
            let k = res.down_heap(l);
            res.up_heap(k, l);
        }

        res
    }

    pub fn push(&mut self, val: T) {
        self.heap.push(val);
        if self.len() < 2 {
            return;
        }
        self.up_heap(self.len() - 1, 1);
    }

    pub fn pop_max(&mut self) -> Option<T> {
        if self.len() < 3 {
            self.heap.pop()
        } else {
            let res = self.heap.swap_remove(1);
            let k = self.down_heap(1);
            self.up_heap(k, 1);
            Some(res)
        }
    }

    pub fn pop_min(&mut self) -> Option<T> {
        if self.len() < 2 {
            self.heap.pop()
        } else {
            let res = self.heap.swap_remove(0);
            let k = self.down_heap(0);
            self.up_heap(k, 1);
            Some(res)
        }
    }

    pub fn max(&self) -> Option<&T> {
        self.heap.get(1).or(self.heap.get(0))
    }

    pub fn min(&self) -> Option<&T> {
        self.heap.get(0)
    }
}
