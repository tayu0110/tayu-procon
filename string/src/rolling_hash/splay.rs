use super::{mul, MOD, POW_CACHE};
use std::cell::Cell;
use std::fmt::Debug;
use std::ops::{Deref, DerefMut, Range};
use std::ptr::NonNull;

#[derive(Clone, Copy)]
struct Node {
    parent: Option<NodeRef>,
    left: Option<NodeRef>,
    right: Option<NodeRef>,
    // forward, reverse, base
    sum: (u64, u64, u64),
    val: u64,
    subsum: u32,
    rev: bool,
}

impl Node {
    pub const fn is_reversed(&self) -> bool {
        self.rev
    }

    pub fn toggle(&mut self) {
        self.rev ^= true;
        self.sum = (self.sum.1, self.sum.0, self.sum.2);
        (self.left, self.right) = (self.right, self.left);
    }

    fn propagate(&mut self) {
        if self.is_reversed() {
            if let Some(mut left) = self.left {
                left.toggle();
            }
            if let Some(mut right) = self.right {
                right.toggle();
            }
        }

        self.rev = false;
    }

    fn update(&mut self) {
        let base = POW_CACHE.lock().unwrap().base();
        self.sum = (self.val, self.val, 1);
        self.subsum = 1;
        if let Some(l) = self.left {
            self.sum.0 += mul(l.sum.0, base);
            self.sum.0 -= MOD & ((self.sum.0 >= MOD) as u64).wrapping_neg();
            self.sum.2 = mul(l.sum.2, base);
            self.sum.1 = mul(self.val, self.sum.2) + l.sum.1;
            self.sum.1 -= MOD & ((self.sum.1 >= MOD) as u64).wrapping_neg();
            self.subsum += l.subsum;
        }
        if let Some(r) = self.right {
            if self.sum.2 == 1 {
                self.sum.2 = mul(r.sum.2, base);
                self.sum.0 = mul(self.val, self.sum.2) + r.sum.0;
                self.sum.0 -= MOD & ((self.sum.0 >= MOD) as u64).wrapping_neg();
                self.sum.1 += mul(r.sum.1, base);
                self.sum.1 -= MOD & ((self.sum.1 >= MOD) as u64).wrapping_neg();
            } else {
                self.sum.0 = mul(self.sum.0, mul(r.sum.2, base)) + r.sum.0;
                self.sum.0 -= MOD & ((self.sum.0 >= MOD) as u64).wrapping_neg();
                self.sum.2 = mul(self.sum.2, base);
                self.sum.1 += mul(r.sum.1, self.sum.2);
                self.sum.1 -= MOD & ((self.sum.1 >= MOD) as u64).wrapping_neg();
                self.sum.2 = mul(self.sum.2, r.sum.2);
            }
            self.subsum += r.subsum;
        }
    }
}

impl Debug for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Node")
            .field("val", &char::from_u32(self.val as u32).unwrap())
            .field("subsum", &self.subsum)
            .field("rev", &self.rev)
            .field("left", &self.left.map(|p| unsafe { p.0.as_ref() }))
            .field("right", &self.right.map(|p| unsafe { p.0.as_ref() }))
            .finish()
    }
}

struct NodeRef(NonNull<Node>);

impl Clone for NodeRef {
    fn clone(&self) -> Self {
        *self
    }
}

impl Copy for NodeRef {}

impl NodeRef {
    fn new(val: char) -> Self {
        let ptr = Box::leak(Box::new(Node {
            parent: None,
            left: None,
            right: None,
            val: val as u64,
            sum: (val as u64, val as u64, 1),
            subsum: 1,
            rev: false,
        }));
        Self(NonNull::new(ptr).unwrap())
    }

    unsafe fn into_raw(self) -> Node {
        let raw = unsafe { Box::from_raw(self.0.as_ptr()) };
        *raw
    }

    fn connect_left(mut self, mut child: Self) {
        child.parent = Some(self);
        self.left = Some(child);
    }

    fn disconnect_left(mut self) -> Option<Self> {
        let mut left = self.left?;
        left.parent = None;
        self.left = None;
        Some(left)
    }

    fn is_left_child(self) -> bool {
        self.parent
            .map_or(false, |p| p.left.map(|p| p.0) == Some(self.0))
    }

    fn connect_right(mut self, mut child: Self) {
        child.parent = Some(self);
        self.right = Some(child);
    }

    fn disconnect_right(mut self) -> Option<Self> {
        let mut right = self.right?;
        right.parent = None;
        self.right = None;
        Some(right)
    }

    fn is_right_child(self) -> bool {
        self.parent
            .map_or(false, |p| p.right.map(|p| p.0) == Some(self.0))
    }

    fn disconnect_parent(self) -> Option<Self> {
        let par = self.parent?;

        if self.is_left_child() {
            par.disconnect_left();
            Some(par)
        } else if self.is_right_child() {
            par.disconnect_right();
            Some(par)
        } else {
            unreachable!()
        }
    }

    fn rotate_left(mut self) -> Self {
        let Some(mut right) = self.disconnect_right() else {
            return self;
        };
        right.sum = self.sum;
        right.subsum = self.subsum;

        if let Some(right_left) = right.disconnect_left() {
            self.connect_right(right_left);
        }

        self.update();

        let self_is_left = self.is_left_child();
        let par = self.disconnect_parent();
        right.connect_left(self);

        if let Some(par) = par {
            if self_is_left {
                par.connect_left(right);
            } else {
                par.connect_right(right);
            }
        }

        // return new root of the original subtree.
        right
    }

    fn rotate_right(mut self) -> Self {
        let Some(mut left) = self.disconnect_left() else {
            return self;
        };
        left.sum = self.sum;
        left.subsum = self.subsum;

        if let Some(left_right) = left.disconnect_right() {
            self.connect_left(left_right);
        }

        self.update();

        let self_is_left = self.is_left_child();
        let par = self.disconnect_parent();
        left.connect_right(self);

        if let Some(par) = par {
            if self_is_left {
                par.connect_left(left);
            } else {
                par.connect_right(left);
            }
        }

        // return new root of the original subtree
        left
    }

    fn splay(mut self) {
        self.propagate();
        while !self.is_root() {
            let &parent = self.parent.as_ref().unwrap();

            if parent.is_root() {
                // zig step
                if self.is_left_child() {
                    parent.rotate_right();
                } else {
                    parent.rotate_left();
                }
                return;
            }

            let &grand_parent = parent.parent.as_ref().unwrap();
            if self.is_left_child() ^ parent.is_left_child() {
                // zig-zag step
                if self.is_left_child() {
                    parent.rotate_right();
                    grand_parent.rotate_left();
                } else if self.is_right_child() {
                    parent.rotate_left();
                    grand_parent.rotate_right();
                } else {
                    unreachable!()
                }
            } else {
                // zig-zig step
                if self.is_left_child() {
                    grand_parent.rotate_right();
                    parent.rotate_right();
                } else if self.is_right_child() {
                    grand_parent.rotate_left();
                    parent.rotate_left();
                } else {
                    unreachable!()
                }
            }
        }
    }

    fn is_root(self) -> bool {
        self.parent.map_or(true, |p| {
            p.left.map_or(true, |s| s.0 != self.0) && p.right.map_or(true, |d| d.0 != self.0)
        })
    }
}

impl Deref for NodeRef {
    type Target = Node;
    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl DerefMut for NodeRef {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut() }
    }
}

impl Debug for NodeRef {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NodeRef")
            .field("ptr", unsafe { self.0.as_ref() })
            .finish()
    }
}

#[derive(Debug)]
pub(super) struct SplayTree {
    root: Option<Cell<NodeRef>>,
}

impl SplayTree {
    pub(super) const fn new() -> Self {
        Self { root: None }
    }

    pub(super) fn len(&self) -> usize {
        self.root.as_ref().map_or(0, |c| c.get().subsum as usize)
    }

    fn nth_node(&self, mut index: usize) -> Option<NodeRef> {
        if index >= self.len() {
            return None;
        }

        index += 1;
        let mut node = self.root.as_ref()?.get();
        let mut seen = 0;
        while seen < index {
            node.propagate();
            if let Some(left) = node.left {
                if left.subsum as usize + seen >= index {
                    node = left;
                    continue;
                }

                seen += left.subsum as usize;
            }

            seen += 1;
            if seen == index {
                break;
            }

            let Some(right) = node.right else { break };
            node = right;
        }
        node.propagate();
        node.splay();
        self.root.as_ref().unwrap().set(node);

        Some(node)
    }

    #[cfg(test)]
    pub(super) fn get(&self, index: usize) -> Option<char> {
        let nth = self.nth_node(index)?;
        char::from_u32(nth.val as u32)
    }

    pub(super) fn insert(&mut self, index: usize, val: char) -> Result<(), &'static str> {
        if self.len() == 0 {
            let new = NodeRef::new(val);
            self.root = Some(Cell::new(new));
            return Ok(());
        }
        if index == self.len() {
            let new = NodeRef::new(val);
            let mut node = self.nth_node(self.len() - 1).unwrap();
            node.splay();
            node.connect_right(new);
            node.update();

            self.root.as_mut().unwrap().set(node);
            return Ok(());
        }

        let back = self.split_off(index)?;
        let mut new = NodeRef::new(val);
        new.connect_left(self.root.as_ref().unwrap().get());
        self.root.as_ref().unwrap().set(new);
        new.update();
        self.extend(back);

        Ok(())
    }

    pub(super) fn remove(&mut self, index: usize) -> Option<char> {
        let mut back = self.split_off(index).ok()?;

        let node = back.nth_node(0)?;
        if let Some(right) = node.disconnect_right() {
            back.root.as_ref().unwrap().set(right);
        } else {
            back.root = None;
        }

        self.extend(back);

        Some(unsafe { char::from_u32(node.into_raw().val as u32)? })
    }

    pub(super) fn split_off(&mut self, at: usize) -> Result<Self, &'static str> {
        if at == 0 {
            let mut res = Self::new();
            std::mem::swap(self, &mut res);
            return Ok(res);
        } else if at == self.len() {
            return Ok(Self::new());
        }

        let mut split_point = self
            .nth_node(at)
            .ok_or("index out of range in SplayTree::split_off")?;
        split_point.propagate();
        let left = split_point.disconnect_left().unwrap();
        split_point.update();

        let res = Self { root: Some(Cell::new(split_point)) };

        self.root.as_mut().unwrap().set(left);
        Ok(res)
    }

    pub(super) fn extend(&mut self, other: Self) {
        if other.root.is_none() {
            return;
        } else if self.root.is_none() {
            self.root = other.root;
            return;
        }

        let mut node = self.nth_node(self.len() - 1).unwrap();

        node.connect_right(other.root.unwrap().get());
        node.update();
        self.root.as_mut().unwrap().set(node);
    }

    pub(super) fn reverse(&mut self, range: Range<usize>) -> Result<(), &'static str> {
        if range.is_empty() {
            return Ok(());
        }

        let Range { start, end } = range;
        let back = self.split_off(end)?;
        let mut mid = self.split_off(start)?;

        let mut mid_root = mid.root.as_mut().unwrap().get();
        mid_root.toggle();
        mid_root.propagate();

        self.extend(mid);
        self.extend(back);

        Ok(())
    }

    pub(super) fn fold(&mut self, range: Range<usize>) -> Result<u64, &'static str> {
        Ok(self.fold_both(range)?.0)
    }

    pub(super) fn fold_reverse(&mut self, range: Range<usize>) -> Result<u64, &'static str> {
        Ok(self.fold_both(range)?.1)
    }

    pub(super) fn fold_both(&mut self, range: Range<usize>) -> Result<(u64, u64), &'static str> {
        if range.is_empty() {
            return Ok((0, 0));
        }

        let Range { start, end } = range;

        let back = self.split_off(end)?;
        let mid = self.split_off(start)?;

        let node = mid.root.as_ref().unwrap().get();
        let res = (node.sum.0, node.sum.1);

        self.extend(mid);
        self.extend(back);

        Ok(res)
    }

    pub(super) fn set(&mut self, index: usize, val: char) -> Result<(), &'static str> {
        let mut node = self
            .nth_node(index)
            .ok_or("index out of range in SplayTree::set")?;
        node.val = val as u64;
        node.update();
        self.root.as_mut().unwrap().set(node);
        Ok(())
    }
}

impl FromIterator<char> for SplayTree {
    fn from_iter<T: IntoIterator<Item = char>>(iter: T) -> Self {
        let mut iter = iter.into_iter();
        let Some(mut node) = iter.next().map(NodeRef::new) else {
            return SplayTree::new();
        };

        for c in iter {
            let new = NodeRef::new(c);
            node.connect_right(new);
            node = new;
        }

        while let Some(mut par) = node.parent {
            par.update();
            node = par;
        }

        SplayTree { root: Some(Cell::new(node)) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_eq(l: Option<NodeRef>, r: Option<NodeRef>) -> bool {
        l.map(|p| p.0) == r.map(|p| p.0)
    }

    #[test]
    fn add_child_test() {
        let a = NodeRef::new('a');
        let b = NodeRef::new('b');
        let c = NodeRef::new('c');

        // make tree as the following
        //      a
        //     / \
        //    b   c
        a.connect_left(b);
        a.connect_right(c);

        assert!(check_eq(a.left, Some(b)));
        assert!(check_eq(a.right, Some(c)));
        assert!(check_eq(b.parent, Some(a)));
        assert!(check_eq(c.parent, Some(a)));
    }

    #[test]
    fn rotate_left_test() {
        let a = NodeRef::new('a');
        let b = NodeRef::new('b');
        let c = NodeRef::new('c');
        let d = NodeRef::new('d');
        let e = NodeRef::new('e');

        // make tree as the following
        //      a
        //     / \
        //    b   c
        //       / \
        //      d   e
        a.connect_left(b);
        a.connect_right(c);
        c.connect_left(d);
        c.connect_right(e);

        // rotate left at node 'a'
        //      c
        //     / \
        //    a   e
        //   / \
        //  b   d
        a.rotate_left();
        assert!(check_eq(a.parent, Some(c)));
        assert!(check_eq(a.left, Some(b)));
        assert!(check_eq(a.right, Some(d)));
        assert!(check_eq(b.parent, Some(a)));
        assert!(check_eq(b.left, None));
        assert!(check_eq(b.right, None));
        assert!(check_eq(c.parent, None));
        assert!(check_eq(c.left, Some(a)));
        assert!(check_eq(c.right, Some(e)));
        assert!(check_eq(d.parent, Some(a)));
        assert!(check_eq(d.left, None));
        assert!(check_eq(d.right, None));
        assert!(check_eq(e.parent, Some(c)));
        assert!(check_eq(e.left, None));
        assert!(check_eq(e.right, None));

        // rotate left at node 'a' again
        //       c
        //      / \
        //     d   e
        //    /
        //   a
        //  /
        // b
        a.rotate_left();
        assert!(check_eq(a.parent, Some(d)));
        assert!(check_eq(a.left, Some(b)));
        assert!(check_eq(a.right, None));
        assert!(check_eq(b.parent, Some(a)));
        assert!(check_eq(b.left, None));
        assert!(check_eq(b.right, None));
        assert!(check_eq(c.parent, None));
        assert!(check_eq(c.left, Some(d)));
        assert!(check_eq(c.right, Some(e)));
        assert!(check_eq(d.parent, Some(c)));
        assert!(check_eq(d.left, Some(a)));
        assert!(check_eq(d.right, None));
        assert!(check_eq(e.parent, Some(c)));
        assert!(check_eq(e.left, None));
        assert!(check_eq(e.right, None));
    }

    #[test]
    fn rotate_right_test() {
        let a = NodeRef::new('a');
        let b = NodeRef::new('b');
        let c = NodeRef::new('c');
        let d = NodeRef::new('d');
        let e = NodeRef::new('e');

        // make tree as the following
        //      a
        //     / \
        //    b   c
        //   / \
        //  d   e
        a.connect_left(b);
        a.connect_right(c);
        b.connect_left(d);
        b.connect_right(e);

        // rotate right at node 'a'
        //      b
        //     / \
        //    d   a
        //       / \
        //      e   c
        a.rotate_right();
        assert!(check_eq(a.parent, Some(b)));
        assert!(check_eq(a.left, Some(e)));
        assert!(check_eq(a.right, Some(c)));
        assert!(check_eq(b.parent, None));
        assert!(check_eq(b.left, Some(d)));
        assert!(check_eq(b.right, Some(a)));
        assert!(check_eq(c.parent, Some(a)));
        assert!(check_eq(c.left, None));
        assert!(check_eq(c.right, None));
        assert!(check_eq(d.parent, Some(b)));
        assert!(check_eq(d.left, None));
        assert!(check_eq(d.right, None));
        assert!(check_eq(e.parent, Some(a)));
        assert!(check_eq(e.left, None));
        assert!(check_eq(e.right, None));

        // rotate right at node 'a' again
        //     b
        //    / \
        //   d   e
        //        \
        //         a
        //          \
        //           c
        a.rotate_right();
        assert!(check_eq(a.parent, Some(e)));
        assert!(check_eq(a.left, None));
        assert!(check_eq(a.right, Some(c)));
        assert!(check_eq(b.parent, None));
        assert!(check_eq(b.left, Some(d)));
        assert!(check_eq(b.right, Some(e)));
        assert!(check_eq(c.parent, Some(a)));
        assert!(check_eq(c.left, None));
        assert!(check_eq(c.right, None));
        assert!(check_eq(d.parent, Some(b)));
        assert!(check_eq(d.left, None));
        assert!(check_eq(d.right, None));
        assert!(check_eq(e.parent, Some(b)));
        assert!(check_eq(e.left, None));
        assert!(check_eq(e.right, Some(a)));
    }

    fn is_left_connected(par: NodeRef, child: NodeRef) -> bool {
        par.left.map(|p| p.0) == Some(child.0) && child.parent.map(|p| p.0) == Some(par.0)
    }

    fn is_right_connected(par: NodeRef, child: NodeRef) -> bool {
        par.right.map(|p| p.0) == Some(child.0) && child.parent.map(|p| p.0) == Some(par.0)
    }

    #[test]
    fn splay_test() {
        let a = NodeRef::new('a');
        let b = NodeRef::new('b');
        let c = NodeRef::new('c');
        let d = NodeRef::new('d');
        let e = NodeRef::new('e');

        //       a
        //      / \
        //     b   c
        //    / \
        //   d   e
        a.connect_left(b);
        a.connect_right(c);
        b.connect_left(d);
        b.connect_right(e);

        //       a
        //      / \
        //     b   c
        //    / \
        //   d   e
        a.splay();
        assert!(check_eq(a.parent, None));
        assert!(is_left_connected(a, b));
        assert!(is_right_connected(a, c));
        assert!(is_left_connected(b, d));
        assert!(is_right_connected(b, e));

        // zig step
        //      b
        //     / \
        //    d   a
        //       / \
        //      e   c
        b.splay();
        assert!(check_eq(b.parent, None));
        assert!(is_left_connected(b, d));
        assert!(is_right_connected(b, a));
        assert!(is_left_connected(a, e));
        assert!(is_right_connected(a, c));

        // zig-zig step
        //        c
        //       /
        //      a
        //     /
        //    b
        //   / \
        //  d   e
        c.splay();
        assert!(check_eq(c.parent, None));
        assert!(is_left_connected(c, a));
        assert!(check_eq(c.right, None));
        assert!(is_left_connected(a, b));
        assert!(check_eq(a.right, None));
        assert!(is_left_connected(b, d));
        assert!(is_right_connected(b, e));

        // zig-zag step
        //         e
        //        / \
        //       b   c
        //      /   /
        //     d   a
        e.splay();
        assert!(check_eq(e.parent, None));
        assert!(is_left_connected(e, b));
        assert!(is_right_connected(e, c));
        assert!(is_left_connected(b, d));
        assert!(is_left_connected(c, a));
    }

    #[test]
    fn insert_test() {
        let mut t = SplayTree::new();
        t.insert(0, 'a').unwrap();

        assert_eq!(t.get(0), Some('a'));

        for i in 1..26 {
            t.insert(i, (b'a' + i as u8) as char).unwrap();
        }

        assert_eq!(t.get(1), Some('b'));
        assert_eq!(t.get(2), Some('c'));
        assert_eq!(t.get(25), Some('z'));
        assert_eq!(t.get(0), Some('a'));
    }

    #[test]
    fn remove_test() {
        let mut t = SplayTree::new();

        for i in 0..26 {
            t.insert(i, (b'a' + i as u8) as char).unwrap();
        }

        assert_eq!(t.remove(0), Some('a'));
        assert_eq!(t.len(), 25);
        assert_eq!(t.remove(0), Some('b'));
        assert_eq!(t.remove(1), Some('d'));
        assert_eq!(t.remove(15), Some('s'));
        eprintln!("t: {t:#?}");
        assert_eq!(t.remove(15), Some('t'));
        assert_eq!(t.len(), 21);
    }

    #[test]
    fn split_test() {
        let mut t = SplayTree::new();
        for i in 0..26 {
            t.insert(i, (b'a' + i as u8) as char).unwrap();
        }

        assert_eq!(t.len(), 26);

        let u = t.split_off(10).unwrap();
        assert_eq!(t.len(), 10);
        assert_eq!(u.len(), 16);
        assert_eq!(u.get(0), Some('k'));
        assert_eq!(t.get(10), None);
        assert_eq!(u.get(1), Some('l'));
        assert_eq!(u.get(15), Some('z'))
    }

    #[test]
    fn split_extend_test() {
        let mut t = SplayTree::new();
        for i in 0..26 {
            t.insert(i, (b'a' + i as u8) as char).unwrap();
        }

        let mut u = t.split_off(10).unwrap();
        assert_eq!(t.len(), 10);
        assert_eq!(u.len(), 16);

        assert_eq!(t.remove(9), Some('j'));
        assert_eq!(t.remove(8), Some('i'));
        assert_eq!(u.remove(0), Some('k'));
        assert_eq!(u.remove(0), Some('l'));

        t.extend(u);

        assert_eq!(t.len(), 22);
        assert_eq!(t.get(7), Some('h'));
        assert_eq!(t.get(8), Some('m'));
    }
}
