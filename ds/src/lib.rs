mod btree_multiset;
mod fixed_ring_queue;
mod interval_heap;

#[cfg(feature = "btree-multiset")]
pub use btree_multiset::*;
#[cfg(feature = "fixed-ring-queue")]
pub use fixed_ring_queue::*;
#[cfg(feature = "double-ended-priority-queue")]
pub use interval_heap::*;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn multiset_test() {
        let mut multiset = BTreeMultiSet::new();
        multiset.insert(0u32);
        assert_eq!(multiset.count(&0), 1);

        multiset.insert(0);
        multiset.insert(0);
        assert_eq!(multiset.count(&0), 3);

        multiset.remove(&0);
        assert_eq!(multiset.count(&0), 2);
        assert!(multiset.has_duplicate());

        multiset.insert(10);
        multiset.insert(2);
        multiset.insert(1);

        assert_eq!(multiset.len(), 5);
        assert_eq!(multiset.last().unwrap(), &10);
        assert!(multiset.contains(&2));
        assert!(!multiset.contains(&3));

        let mut iter = multiset.iter();
        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&10));
        assert_eq!(iter.next(), None);

        let mut range = multiset.range(1..);
        assert_eq!(range.next(), Some(&1));
        assert_eq!(range.next(), Some(&2));
        assert_eq!(range.next(), Some(&10));
        assert_eq!(range.next(), None);

        multiset.remove_all(&0);
        assert!(!multiset.contains(&0));
        assert_eq!(multiset.len(), 3);
        assert!(!multiset.has_duplicate());
    }

    #[test]
    fn ring_queue_test() {
        const SIZE: usize = 1 << 5;
        let mut nt = FixedRingQueue::<i32, SIZE>::new();

        assert!(nt.is_empty());

        nt.push(1);
        nt.push(2);
        nt.push(10);
        nt.push(5);

        assert_eq!(nt.len(), 4);
        assert!(!nt.is_full());
        assert_eq!(nt.pop().expect("why queue is empty?"), 1);

        for i in 0..(1 << 5) - 3 {
            nt.push(i);
        }

        assert!(nt.is_full());

        assert_eq!(nt.pop().expect("why queue is empty"), 2);
        assert_eq!(nt.pop().expect("why queue is empty"), 10);
        assert_eq!(nt.pop().expect("why queue is empty"), 5);
        assert_eq!(nt.pop().expect("why queue is empty"), 0);

        while nt.pop().is_some() {}

        assert!(nt.is_empty());
    }
}
