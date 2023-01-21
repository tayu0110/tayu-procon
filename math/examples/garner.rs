// https://yukicoder.me/problems/448
use iolib::scan;
use math::garner_prechecked;

const MOD: i64 = 1000_000_007;

fn main() {
    scan!(n: usize, p: [(i64, i64); n]);

    let (a, p) = p.into_iter().unzip::<i64, i64, Vec<_>, Vec<_>>();

    let f = a.iter().all(|a| *a == 0);

    if let Some((res, lcm)) = garner_prechecked(&a, &p, MOD) {
        if f {
            println!("{}", lcm)
        } else {
            println!("{}", res)
        }
    } else {
        println!("-1")
    }
}
