// https://atcoder.jp/contests/tenka1-2016-quala/tasks/tenka1_2016_qualA_c
use cpgraph::FixedGraph;
use cpio::*;

fn main() {
    scan!(n: usize, e: [(String, String); n]);

    let mut edges = vec![];
    'b: for (a, b) in e {
        for (a, b) in a.chars().zip(b.chars()) {
            if a != b {
                edges.push((a as usize - b'a' as usize, b as usize - b'a' as usize));
                continue 'b;
            }
        }

        if a.len() > b.len() {
            putln!(-1);
            return;
        }
    }
    let graph = FixedGraph::<(), true>::from((26, edges));

    if let Some(res) = graph.topological_sort() {
        putln!(res
            .into_iter()
            .map(|a| (a as u8 + b'a') as char)
            .collect::<String>());
    } else {
        putln!(-1);
    }
}
