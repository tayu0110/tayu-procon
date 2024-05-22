#[cfg(feature = "btree-multiset")]
mod btree_multiset;
#[cfg(feature = "cartesian-tree")]
mod cartesian_tree;
#[cfg(feature = "dynamic-sequence")]
mod dynamic_sequence;
#[cfg(feature = "euler-tour-tree")]
mod euler_tour_tree;
#[cfg(feature = "fixed-ring-queue")]
mod fixed_ring_queue;
#[cfg(feature = "double-ended-priority-queue")]
mod interval_heap;
#[cfg(feature = "link-cut-tree")]
mod link_cut_tree;
#[cfg(feature = "online-dynamic-connectivity")]
mod online_dynamic_connectivity;
#[cfg(feature = "splay-tree")]
mod splay_tree;
#[cfg(feature = "wavelet-matrix")]
mod wavelet_matrix;

use std::ops::{Bound, Range, RangeBounds};

#[cfg(feature = "btree-multiset")]
pub use btree_multiset::*;
#[cfg(feature = "cartesian-tree")]
pub use cartesian_tree::*;
#[cfg(feature = "dynamic-sequence")]
pub use dynamic_sequence::*;
#[cfg(feature = "euler-tour-tree")]
pub use euler_tour_tree::*;
#[cfg(feature = "fixed-ring-queue")]
pub use fixed_ring_queue::*;
#[cfg(feature = "double-ended-priority-queue")]
pub use interval_heap::*;
#[cfg(feature = "link-cut-tree")]
pub use link_cut_tree::*;
#[cfg(feature = "online-dynamic-connectivity")]
pub use online_dynamic_connectivity::*;
#[cfg(feature = "wavelet-matrix")]
pub use wavelet_matrix::*;

pub trait MapMonoid {
    type M;
    type Act;

    fn e() -> Self::M;
    fn op(l: &Self::M, r: &Self::M) -> Self::M;
    fn id() -> Self::Act;
    fn composite(l: &Self::Act, r: &Self::Act) -> Self::Act;
    fn map(m: &Self::M, act: &Self::Act) -> Self::M;
    /// If the `M` operation is not commutative (i.e., `MapMonoid::op` is not commutative), implement `reverse`.
    fn reverse(m: &mut Self::M) {
        let _ = m;
    }
}

fn convert_range(len: usize, range: impl RangeBounds<usize>) -> Range<usize> {
    let start = match range.start_bound() {
        Bound::Included(l) => *l,
        Bound::Unbounded => 0,
        _ => unreachable!(),
    };
    let end = match range.end_bound() {
        Bound::Included(r) => r + 1,
        Bound::Excluded(r) => *r,
        Bound::Unbounded => len,
    };
    Range { start, end }
}

/// If the Link-Cut Tree does not require any operations, this type can be used as a dummy.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct DefaultZST;

impl MapMonoid for DefaultZST {
    type M = ();
    type Act = ();

    fn e() -> Self::M {}
    fn op(_: &Self::M, _: &Self::M) -> Self::M {}
    fn map(_: &Self::M, _: &Self::Act) -> Self::M {}
    fn id() -> Self::Act {}
    fn composite(_: &Self::Act, _: &Self::Act) -> Self::Act {}
}
