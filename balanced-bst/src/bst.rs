use std::cell::Cell;
use std::ops::{Deref, DerefMut};
use std::ptr::NonNull;

struct Node<T> {
    parent: Option<NodeRef<T>>,
    left: Option<NodeRef<T>>,
    right: Option<NodeRef<T>>,
    val: T,
}

impl<T> Node<T> {
    pub fn new(val: T) -> Self {
        Self { parent: None, left: None, right: None, val }
    }
}

#[derive(Debug)]
struct NodeRef<T>(NonNull<Node<T>>);

impl<T> NodeRef<T> {
    pub fn new(node: Node<T>) -> Self {
        let reference = Box::leak(Box::new(node));
        Self(NonNull::new(reference as *mut _).unwrap())
    }

    /// # Safety
    /// * This function must be called **ONLY ONCE**.
    /// * Since this function call, the Node<T> referenced by NodeRef<T> will be dropped and may return values that are not normal.
    pub unsafe fn into_raw(self) -> Node<T> {
        let bx = Box::from_raw(self.0.as_ptr());
        *bx
    }

    pub fn connect_left(&mut self, mut child: Self) {
        self.left = Some(child);
        child.parent = Some(*self);
    }

    pub fn connect_right(&mut self, mut child: Self) {
        self.right = Some(child);
        child.parent = Some(*self);
    }

    pub fn disconnect_left(&mut self) -> Option<Self> {
        if let Some(mut left) = self.left {
            left.parent = None;
            self.left = None;
            Some(left)
        } else {
            None
        }
    }

    pub fn disconnect_right(&mut self) -> Option<Self> {
        if let Some(mut right) = self.right {
            right.parent = None;
            self.right = None;
            Some(right)
        } else {
            None
        }
    }

    pub fn disconnect_parent(&mut self) -> Option<Self> {
        if let Some(mut parent) = self.parent {
            match (parent.left, parent.right) {
                (Some(l), _) if l.0 == self.0 => {
                    parent.left = None;
                    self.parent = None;
                }
                (_, Some(r)) if r.0 == self.0 => {
                    parent.right = None;
                    self.parent = None;
                }
                _ => {
                    unreachable!()
                }
            }

            Some(parent)
        } else {
            None
        }
    }
}

impl<T: Ord> NodeRef<T> {
    pub fn try_connect_child(&mut self, child: Self) -> Result<(), &'static str> {
        if self.val < child.val {
            if self.left.is_some() {
                return Err("Left child already exists.");
            }
            self.connect_left(child);
        } else if self.val > child.val {
            if self.right.is_some() {
                return Err("Right child is already exists");
            }
            self.connect_right(child);
        } else {
            return Err("Duplicate Node");
        }

        Ok(())
    }
}

impl<T> Clone for NodeRef<T> {
    fn clone(&self) -> Self {
        *self
    }
}

impl<T> Copy for NodeRef<T> {}

impl<T> Deref for NodeRef<T> {
    type Target = Node<T>;

    fn deref(&self) -> &Self::Target {
        unsafe { self.0.as_ref() }
    }
}

impl<T> DerefMut for NodeRef<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { self.0.as_mut() }
    }
}

pub struct BinarySearchTree<T> {
    root: Option<Cell<NodeRef<T>>>,
}

impl<T: Ord> BinarySearchTree<T> {
    pub const fn new() -> Self {
        Self { root: None }
    }

    pub fn contains(&self, val: &T) -> bool {
        self.get(val).is_some()
    }

    pub fn get(&self, val: &T) -> Option<&T> {
        let mut node = self.root.as_ref()?.get();

        while &node.val != val {
            if val < &node.val {
                let Some(next) = node.left else { break };
                node = next;
            } else {
                let Some(next) = node.right else { break };
                node = next;
            }
        }

        unsafe { (&node.0.as_ref().val == val).then_some(&node.0.as_ref().val) }
    }

    pub fn insert(&mut self, val: T) {
        if let Some(mut node) = self.root.as_ref().map(|c| c.get()) {
            while node.val != val {
                if val < node.val {
                    if let Some(left) = node.left {
                        node = left;
                    } else {
                        let new = NodeRef::new(Node::new(val));
                        node.connect_left(new);
                        return;
                    }
                } else {
                    if let Some(right) = node.right {
                        node = right;
                    } else {
                        let new = NodeRef::new(Node::new(val));
                        node.connect_right(new);
                        return;
                    }
                }
            }
        } else {
            let new = NodeRef::new(Node::new(val));
            self.root = Some(Cell::new(new));
        }
    }

    pub fn remove(&mut self, val: &T) -> Option<T> {
        let mut node = self.root.as_ref()?.get();

        while &node.val != val {
            if val < &node.val {
                let Some(left) = node.left else {
                    break;
                };
                node = left;
            } else {
                let Some(right) = node.right else { break };
                node = right;
            }
        }

        if &node.val != val {
            return None;
        }

        match (node.disconnect_left(), node.disconnect_right()) {
            (Some(left), Some(mut right)) => {
                if let Some(mut right_most_left) = right.left {
                    while let Some(l) = right_most_left.left {
                        right_most_left = l;
                    }
                    let mut p = right_most_left.disconnect_parent().unwrap();
                    if let Some(r) = right_most_left.disconnect_right() {
                        p.connect_left(r);
                    }

                    right_most_left.connect_left(left);
                    right_most_left.connect_right(right);

                    if let Some(mut par) = node.disconnect_parent() {
                        par.try_connect_child(right_most_left).unwrap();
                    } else {
                        self.root.as_mut().unwrap().replace(right_most_left);
                    }
                } else {
                    right.connect_left(left);
                    if let Some(mut par) = node.disconnect_parent() {
                        par.try_connect_child(right).unwrap();
                    } else {
                        self.root.as_mut().unwrap().replace(right);
                    }
                }
            }
            (Some(c), None) | (None, Some(c)) => {
                if let Some(mut par) = node.disconnect_parent() {
                    par.try_connect_child(c).unwrap();
                } else {
                    self.root.as_mut().unwrap().replace(c);
                }
            }
            (None, None) => {
                let par = node.disconnect_parent();
                if par.is_none() {
                    self.root = None;
                }
            }
        }

        unsafe { Some(node.into_raw().val) }
    }
}

impl<T: Ord> Default for BinarySearchTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bst_test() {
        let mut tree = BinarySearchTree::new();
        tree.insert(0);

        assert!(tree.contains(&0));

        tree.insert(10);
        tree.insert(20);
        tree.insert(30);

        assert!(tree.contains(&10));
        assert!(tree.contains(&20));
        assert!(tree.contains(&30));
        assert!(!tree.contains(&40));

        let res = tree.remove(&20);
        assert!(!tree.contains(&20));
        assert!(res.is_some());
        assert_eq!(res.unwrap(), 20);
    }
}
