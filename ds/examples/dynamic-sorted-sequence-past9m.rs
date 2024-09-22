use std::borrow::Cow;

use cpio::*;
use ds::{DynamicSortedSequence, MapMonoid};

#[derive(Clone)]
struct T;
impl MapMonoid for T {
    type M = (Cow<'static, str>, usize);
    type Act = ();

    fn e() -> Self::M {
        ("".into(), usize::MAX)
    }
    fn op(_: &Self::M, _: &Self::M) -> Self::M {
        ("".into(), usize::MAX)
    }

    fn id() -> Self::Act {}
    fn composite(_: &Self::Act, _: &Self::Act) -> Self::Act {}

    fn map(_: &Self::M, _: &Self::Act) -> Self::M {
        ("".into(), usize::MAX)
    }
}

fn main() {
    scan! {n: usize, q: usize, s: [String; n]}

    let mut seq = s
        .into_iter()
        .enumerate()
        .map(|(i, s)| (s.into(), i))
        .collect::<DynamicSortedSequence<T>>();
    for _ in 0..q {
        scan! {x: usize, t: String}

        let (_, index) = seq.remove(x - 1);
        seq.insert((t.into(), index));
    }

    let mut seq = seq
        .into_iter()
        .map(|s| (s.0.as_ref().to_owned(), s.1))
        .collect::<Vec<_>>();
    seq.sort_by_key(|s| s.1);
    putln!(seq.into_iter().map(|v| v.0), @sep = " ");
}
