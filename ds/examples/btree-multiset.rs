// https://atcoder.jp/contests/abc308/tasks/abc308_g
use ds::BTreeMultiSet;
use proconio::*;

fn main() {
    input! {q: usize}

    let mut min = BTreeMultiSet::new();

    let mut multiset = BTreeMultiSet::new();

    for _ in 0..q {
        input! {t: usize}

        if t == 1 {
            input! {x: usize}
            if !multiset.contains(&x) {
                if let (Some(k), Some(k2)) =
                    (multiset.range(x..).next(), multiset.range(..=x).next_back())
                {
                    min.insert(k ^ x);
                    min.insert(k2 ^ x);
                    min.remove(&(k ^ k2));
                } else if let Some(k) = multiset.range(x..).next() {
                    min.insert(k ^ x);
                } else if let Some(k) = multiset.range(..=x).next_back() {
                    min.insert(k ^ x);
                }
            }

            multiset.insert(x);
        } else if t == 2 {
            input! {x: usize}
            multiset.remove(&x);
            if multiset.count(&x) == 0 {
                if let (Some(k), Some(k2)) =
                    (multiset.range(x..).next(), multiset.range(..=x).next_back())
                {
                    min.remove(&(k ^ x));
                    min.remove(&(k2 ^ x));
                    min.insert(k ^ k2);
                } else if let Some(k) = multiset.range(x..).next() {
                    min.remove(&(k ^ x));
                } else if let Some(k) = multiset.range(..=x).next_back() {
                    min.remove(&(k ^ x));
                }
            }
        } else if multiset.has_duplicate() {
            println!("0");
        } else {
            println!("{}", min.first().unwrap());
        }
    }
}
