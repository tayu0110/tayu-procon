use cpio::*;
use math::enumerate_quotients;

fn main() {
    scan!(n: u64);

    let res = enumerate_quotients(n).map(|res| res.0).collect::<Vec<_>>();
    putln!(res.len());
    putln!(res, @sep = " ");
}
