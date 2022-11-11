use suffix_array::SuffixArray;

fn main() {
    use std::io::BufRead;
    let stdin = std::io::stdin();
    let mut stdin = std::io::BufReader::new(stdin.lock());
    let mut s = String::new();
    stdin.read_line(&mut s).unwrap();
    s.pop();

    use std::io::Write;
    let stdout = std::io::stdout();
    let mut stdout = std::io::BufWriter::new(stdout.lock());

    let sa = SuffixArray::new(&s);
    let lcpa = sa.lcp_array();

    writeln!(stdout, "{}", s.len() * (s.len() + 1) / 2 - lcpa.into_iter().sum::<usize>()).unwrap();
}