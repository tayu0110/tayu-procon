use iolib::scan;

fn main() {
    scan!(
        n: usize,
        m: usize,
        p: [[[(usize, usize, i64); 2]; 2]; m / 4]
    );

    let mut t = vec![vec![]; n];
    for (u, v, w) in p.into_iter().flatten().flatten() {
        t[u].push((v, w));
    }

    let mut dist = vec![std::i64::MAX; n];
    dist[0] = 0;
    for i in 0..=n {
        for from in 0..n {
            for &(to, w) in &t[from] {
                if i == n {
                    if dist[to] > dist[from].saturating_add(w) {
                        println!("Negative Cycle is detected.");
                        println!("dist: {:?}", dist);
                        return;
                    }
                } else {
                    dist[to] = std::cmp::min(dist[to], dist[from].saturating_add(w));
                }
            }
        }
    }

    for (i, dist) in dist.into_iter().enumerate() {
        println!("0->{}: {}", i, dist);
    }
}
