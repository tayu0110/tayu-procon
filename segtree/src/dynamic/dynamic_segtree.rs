use super::{super::convert_range_isize, Monoid, Node, Zst};
use std::ops::{Range, RangeBounds};

type SegtreeNode<T> = Node<T, Zst>;

pub struct DynamicSegmentTree<T: Monoid> {
    range: Range<isize>,
    nodes: Vec<SegtreeNode<T::M>>,
}

impl<T: Monoid> DynamicSegmentTree<T> {
    pub fn new(range: impl RangeBounds<isize>) -> Self {
        Self {
            range: convert_range_isize(isize::MIN, isize::MAX, range),
            nodes: vec![SegtreeNode::new(T::id(), Zst)],
        }
    }

    pub fn len(&self) -> usize {
        self.range.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    fn create_node(&mut self) -> u32 {
        let res = self.nodes.len();
        let node = SegtreeNode::new(T::id(), Zst);

        self.nodes.push(node);
        res as u32
    }

    fn do_set(&mut self, index: isize, val: T::M, l: isize, r: isize, now: usize) {
        if r - l == 1 {
            self.nodes[now].val = val;
            return;
        }

        let mid = (r + l) >> 1;
        if index < mid {
            if self.nodes[now].left == u32::MAX {
                self.nodes[now].left = self.create_node();
            }
            self.do_set(index, val, l, mid, self.nodes[now].left as usize);
        } else {
            if self.nodes[now].right == u32::MAX {
                self.nodes[now].right = self.create_node();
            }
            self.do_set(index, val, mid, r, self.nodes[now].right as usize);
        }

        let SegtreeNode { left, right, .. } = self.nodes[now];
        self.nodes[now].val = T::op(
            self.nodes.get(left as usize).map_or(&T::id(), |n| &n.val),
            self.nodes.get(right as usize).map_or(&T::id(), |n| &n.val),
        );
    }

    pub fn set(&mut self, index: isize, val: T::M) {
        assert!(self.range.contains(&index));

        self.do_set(index, val, self.range.start, self.range.end, 0);
    }

    fn do_fold(&self, start: isize, end: isize, l: isize, r: isize, now: u32) -> T::M {
        if now == u32::MAX || l >= r {
            return T::id();
        }
        if start <= l && r <= end {
            return T::op(&self.nodes[now as usize].val, &T::id());
        }
        if r <= start || end <= l {
            return T::id();
        }

        let mid = (r + l) / 2;
        let lv = self.do_fold(start, end, l, mid, self.nodes[now as usize].left);
        let rv = self.do_fold(start, end, mid, r, self.nodes[now as usize].right);
        T::op(&lv, &rv)
    }

    pub fn fold(&self, range: impl RangeBounds<isize>) -> T::M {
        let Range { start, end } = convert_range_isize(self.range.start, self.range.end, range);

        self.do_fold(start, end, self.range.start, self.range.end, 0)
    }
}
