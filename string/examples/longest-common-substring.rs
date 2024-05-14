// https://judge.yosupo.jp/problem/longest_common_substring
use iolib::*;
use string::longest_common_substring;

fn main() {
    scan!(s: String, t: String);

    let (s, t) = longest_common_substring(&s, &t)
        .next()
        .unwrap_or((0..0, 0..0));
    putitln!([s.start, s.end, t.start, t.end].into_iter(), sep = ' ');
}
