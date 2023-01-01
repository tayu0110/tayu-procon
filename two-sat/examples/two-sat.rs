use proconio::input;
use two_sat::TwoSAT;

fn main() {
    input! {n: usize, d: usize, p: [(usize, usize); n]}

    let mut ts = TwoSAT::new(n);

    for (i, &(x, y)) in p.iter().enumerate() {
        for (j, &(nx, ny)) in p.iter().enumerate().skip(i + 1) {
            if std::cmp::max(x, nx) - std::cmp::min(x, nx) < d {
                ts.add_clause(i, false, j, false);
            }
            if std::cmp::max(x, ny) - std::cmp::min(x, ny) < d {
                ts.add_clause(i, false, j, true);
            }
            if std::cmp::max(y, nx) - std::cmp::min(y, nx) < d {
                ts.add_clause(i, true, j, false);
            }
            if std::cmp::max(y, ny) - std::cmp::min(y, ny) < d {
                ts.add_clause(i, true, j, true);
            }
        }
    }

    if !ts.satisfiable() {
        println!("No");
        return;
    }

    println!("Yes");
    let res = ts.answer();
    for (i, &res) in res.into_iter().enumerate() {
        if res {
            println!("{}", p[i].0);
        } else {
            println!("{}", p[i].1);
        }
    }
}
