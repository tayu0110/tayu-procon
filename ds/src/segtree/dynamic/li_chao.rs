use super::{convert_range_isize, Node, Zst};
use std::ops::{Range, RangeBounds};

#[derive(Debug, Clone, Copy)]
pub struct Affine {
    a: isize,
    b: isize,
}

impl Affine {
    fn eval(self, x: isize) -> isize {
        self.a.saturating_mul(x).saturating_add(self.b)
    }
}

impl From<(isize, isize)> for Affine {
    fn from(value: (isize, isize)) -> Self {
        Affine { a: value.0, b: value.1 }
    }
}

type LiChaoTreeNode = Node<Affine, Zst>;

pub struct LiChaoTree {
    range: Range<isize>,
    nodes: Vec<LiChaoTreeNode>,
}

impl LiChaoTree {
    pub fn new(range: impl RangeBounds<isize>) -> Self {
        Self {
            range: convert_range_isize(isize::MIN, isize::MAX, range),
            nodes: vec![LiChaoTreeNode::new((0, isize::MAX).into(), Zst)],
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
        let node = LiChaoTreeNode::new((0, isize::MAX).into(), Zst);

        self.nodes.push(node);
        res as u32
    }

    fn do_add_line(&mut self, val: Affine, l: isize, r: isize, now: usize) {
        if r - l == 1 {
            if val.eval(l) < self.nodes[now].val.eval(l) {
                self.nodes[now].val = val;
            }
            return;
        }

        let (nl, nr) = (val.eval(l), val.eval(r));
        let (pl, pr) = (self.nodes[now].val.eval(l), self.nodes[now].val.eval(r));

        if nl <= pl && nr <= pr {
            self.nodes[now].val = val;
            return;
        }

        if nl >= pl && nr >= pr {
            return;
        }

        let mid = (r + l) >> 1;

        if self.nodes[now].left == u32::MAX {
            let left = self.create_node();
            self.nodes[now].left = left;
            self.nodes[left as usize].val = val;
        } else {
            self.do_add_line(val, l, mid, self.nodes[now].left as usize);
        }
        if self.nodes[now].right == u32::MAX {
            let right = self.create_node();
            self.nodes[now].right = right;
            self.nodes[right as usize].val = val;
        } else {
            self.do_add_line(val, mid, r, self.nodes[now].right as usize);
        }
    }

    #[inline]
    pub fn add_line(&mut self, val: impl Into<Affine>) {
        self.do_add_line(val.into(), self.range.start, self.range.end, 0);
    }

    fn do_add_segment(
        &mut self,
        val: Affine,
        start: isize,
        end: isize,
        l: isize,
        r: isize,
        now: usize,
    ) {
        if start <= l && r <= end {
            self.do_add_line(val, l, r, now);
            return;
        }

        if r <= start || end <= l {
            return;
        }

        let mid = (r + l) >> 1;
        if start < mid {
            if self.nodes[now].left == u32::MAX {
                self.nodes[now].left = self.create_node();
            }
            self.do_add_segment(val, start, end, l, mid, self.nodes[now].left as usize);
        }
        if mid <= end {
            if self.nodes[now].right == u32::MAX {
                self.nodes[now].right = self.create_node();
            }
            self.do_add_segment(val, start, end, mid, r, self.nodes[now].right as usize);
        }
    }

    #[inline]
    pub fn add_segment(&mut self, val: impl Into<Affine>, range: impl RangeBounds<isize>) {
        let Range { start, end } = convert_range_isize(self.range.start, self.range.end, range);

        self.do_add_segment(val.into(), start, end, self.range.start, self.range.end, 0);
    }

    fn do_evaluate(&self, x: isize, l: isize, r: isize, now: u32) -> isize {
        if l >= r || now == u32::MAX {
            return isize::MAX;
        }

        let mut res = self.nodes[now as usize].val.eval(x);
        if r - l == 1 {
            return res;
        }

        let mid = (r + l) >> 1;
        if x < mid {
            res = res.min(self.do_evaluate(x, l, mid, self.nodes[now as usize].left));
        } else {
            res = res.min(self.do_evaluate(x, mid, r, self.nodes[now as usize].right));
        }

        res
    }

    pub fn evaluate(&self, x: isize) -> isize {
        self.do_evaluate(x, self.range.start, self.range.end, 0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn line_add_get_min_test() {
        let mut lct = LiChaoTree::new(-1_000_000_010..1_000_000_010isize);
        lct.add_line((-1, -1));
        lct.add_line((0, 1));

        assert_eq!(lct.evaluate(-1), 0);
        assert_eq!(lct.evaluate(-2), 1);
        assert_eq!(lct.evaluate(0), -1);
        assert_eq!(lct.evaluate(2), -3);
        lct.add_line((0, -10));
        assert_eq!(lct.evaluate(-2), -10);
        assert_eq!(lct.evaluate(0), -10);
        assert_eq!(lct.evaluate(2), -10);
    }
}
