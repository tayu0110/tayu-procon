// https://yukicoder.me/problems/447
use iolib::scan;
use math::chinese_remainder_theorem;

fn main() {
    scan!(x1: i64, y1: i64, x2: i64, y2: i64, x3: i64, y3: i64);

    if let Some((x4, y4)) = chinese_remainder_theorem(x1, y1, x2, y2) {
        match chinese_remainder_theorem(x3, y3, x4, y4) {
            Some((res, lcm)) if res == 0 => println!("{}", lcm),
            Some((res, _)) => println!("{}", res),
            None => println!("-1"),
        }
    } else {
        println!("-1");
    }
}
