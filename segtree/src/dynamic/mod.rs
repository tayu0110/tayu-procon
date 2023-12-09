mod li_chao;
mod segtree;

use super::Monoid;
pub use li_chao::*;
pub use segtree::*;

struct Node<T, L> {
    left: u32,
    right: u32,
    val: T,
    _lazy: L,
}

impl<T, L> Node<T, L> {
    fn new(val: T, lazy: L) -> Self {
        Self { left: u32::MAX, right: u32::MAX, val, _lazy: lazy }
    }
}

#[derive(Debug, Clone, Copy)]
struct Zst;

impl Monoid for Zst {
    type M = Self;
    fn id() -> Self::M {
        Zst
    }
    fn op(_: &Self::M, _: &Self::M) -> Self::M {
        Zst
    }
}
