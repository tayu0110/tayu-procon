// https://judge.yosupo.jp/problem/suffixarray
use iolib::scan;
use suffix_array::SuffixArray;

fn main() {
    scan!(s: String);

    let sa = SuffixArray::new(s);

    let sa = sa.get_sa();

    for (i, sa) in sa.into_iter().enumerate() {
        if i > 0 {
            print!(" ");
        }
        print!("{}", sa);
    }
    println!("");
}
