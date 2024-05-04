use ds::BTreeMultiSet;

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

    {
        let mut iter = multiset.iter();
        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next(), Some(&0));
        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&10));
        assert_eq!(iter.next(), None);
    }

    {
        let mut range = multiset.range(1..);
        assert_eq!(range.next(), Some(&1));
        assert_eq!(range.next(), Some(&2));
        assert_eq!(range.next(), Some(&10));
        assert_eq!(range.next(), None);
    }

    multiset.remove_all(&0);
    assert!(!multiset.contains(&0));
    assert_eq!(multiset.len(), 3);
    assert!(!multiset.has_duplicate());
}
