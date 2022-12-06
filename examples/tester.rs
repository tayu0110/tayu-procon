fn main() {
    proconio::input! {s: proconio::marker::Chars}

    let len = s.len();

    let mut suffixes = (0..len).map(|i| s[i..].into_iter().collect::<String>()).enumerate().collect::<Vec<_>>();
    suffixes.sort_by_key(|(_, s)| s.clone());
    let (sa, _) = suffixes.into_iter().unzip::<usize, String, Vec<usize>, Vec<_>>();

    for (i, sa) in sa.into_iter().enumerate() {
        if i > 0 {
            print!(" ");
        }
        print!("{}", sa);
    }
    println!("");
}
