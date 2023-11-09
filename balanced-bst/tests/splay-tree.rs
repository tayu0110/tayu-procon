use balanced_bst::SplayTreeMap;
use rand::{thread_rng, Rng};

const K: usize = 10;
const Q: usize = 50;

#[test]
fn map_random_test() {
    let mut rng = thread_rng();

    for _ in 0..1000 {
        let mut tree = SplayTreeMap::new();
        let mut array = vec![0; K];
        let mut query = vec![];
        for _ in 0..Q {
            let ty = rng.gen_bool(0.4) as usize;
            if ty == 0 {
                let (k, v) = (rng.gen_range(0..K) as u64, rng.gen_range(0..5));
                query.push((ty, k, v));
            } else {
                let k = rng.gen_range(0..K) as u64;
                query.push((ty, k, 0));
            }
        }

        println!("----- query -----");
        for &(ty, k, v) in &query {
            println!("ty: {ty}, k: {k}, v: {v}");
        }
        println!("-----------------");

        for (ty, k, v) in query {
            if ty == 0 {
                tree.insert(k, v);
                array[k as usize] = v;
            } else {
                assert_eq!(*tree.get(&k).unwrap_or(&0), array[k as usize]);
            }
        }
    }
}
