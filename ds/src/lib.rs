#[cfg(feature = "btree-multiset")]
mod btree_multiset;
#[cfg(feature = "cartesian-tree")]
mod cartesian_tree;
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
#[cfg(feature = "stern-brocot-tree")]
mod stern_brocot_tree;

#[cfg(feature = "btree-multiset")]
pub use btree_multiset::*;
#[cfg(feature = "cartesian-tree")]
pub use cartesian_tree::*;
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
#[cfg(feature = "stern-brocot-tree")]
pub use stern_brocot_tree::*;

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
