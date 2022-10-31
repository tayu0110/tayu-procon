// use tayu_procon::{
//     scan,
//     numeric::factorize
// };

#![allow(dead_code)]

use numeric::factorize;

fn main() {
    use std::io::Write;
    let out = std::io::stdout();
    let mut out = std::io::BufWriter::new(out.lock());

    scan!(q: usize, a: [u64; q]);

    for a in a {
        let mut f = factorize(a);
        f.sort();

        write!(out, "{}", f.len()).unwrap();
        for f in f {
            write!(out, " {}", f).unwrap();
        }
        writeln!(out, "").unwrap();
    }
}

mod iolib {
use std::cell::RefCell;
use std::io::{
    Read, BufRead,
    Error
};
use std::str::SplitWhitespace;
use std::thread_local;

thread_local! {
    static BUF_SPLIT_WHITESPACE: RefCell<SplitWhitespace<'static>> = RefCell::new("".split_whitespace());
}

#[inline]
fn refill_buffer(interactive: bool) -> Result<(), Error> {
    let mut s = String::new();
    
    if cfg!(debug_assertions) || interactive {
        std::io::stdin().lock().read_line(&mut s)?;
    } else {
        std::io::stdin().lock().read_to_string(&mut s)?;
    }

    BUF_SPLIT_WHITESPACE.with(|buf_str| {
        *buf_str.borrow_mut() = Box::leak(s.into_boxed_str()).split_whitespace();
        Ok(())
    })
}

#[inline]
pub fn scan_string(interactive: bool) -> &'static str {
    BUF_SPLIT_WHITESPACE.with(|buf_str| {
        if let Some(s) = buf_str.borrow_mut().next() {
            return s;
        }

        refill_buffer(interactive).unwrap();

        if let Some(s) = buf_str.borrow_mut().next() {
            return s;
        }

        unreachable!("Read Error: No input items.");
    })
}

#[macro_export]
macro_rules! scan {
    // Terminator
    ( @interactive : $interactive:literal ) => {};
    // Terminator
    ( @interactive : $interactive:literal, ) => {};
    // Vec<Vec<....>>
    ( @interactive : $interactive:literal, $v: ident : [ [ $( $inner:tt )+ ] ; $len:expr ]) => {
        let $v = {
            let len = $len;
            (0..len).fold(vec![], |mut v, _| {
                $crate::scan!(@interactive: $interactive, w: [ $( $inner )+ ]);
                v.push(w);
                v
            })
        };
    };
    // Vec<Vec<....>>, ......
    ( @interactive : $interactive:literal, $v: ident : [ [ $( $inner:tt )+ ] ; $len:expr ] , $( $rest:tt )* ) => {
        $crate::scan!(@interactive: $interactive, [ [ $( $inner )+ ] ; $len ]);
        $crate::scan!(@interactive: $interactive, $( $rest )*);
    };
    // Vec<$t>
    ( @interactive : $interactive:literal, $v:ident : [ $t:tt ; $len:expr ]) => {
        let $v = {
            let len = $len;
            (0..len).map(|_| { $crate::scan!(@interactive: $interactive, $v : $t); $v }).collect::<Vec<_>>()
        };
    };
    // Vec<$t>, .....
    ( @interactive : $interactive:literal, $v:ident : [ $t:tt ; $len:expr ] , $( $rest:tt )* ) => {
        let $v = {
            let len = $len;
            (0..len).map(|_| { $crate::scan!(@interactive: $interactive, $v : $t); $v }).collect::<Vec<_>>()
        };
        $crate::scan!(@interactive: $interactive, $( $rest )*);
    };
    // Expand tuple
    ( @interactive : $interactive:literal, @expandtuple, ( $t:tt )) => {
        { let tmp = $crate::iolib::scan_string($interactive).parse::<$t>().unwrap(); tmp }
    };
    // Expand tuple
    ( @interactive : $interactive:literal, @expandtuple, ( $t:tt $( , $rest:tt )* ) ) => {
        (
            $crate::scan!(@interactive: $interactive, @expandtuple, ( $t )),
            $( $crate::scan!(@interactive: $interactive, @expandtuple, ( $rest )), )*
        )
    };
    // let $v: ($t, $u, ....) = (.......)
    ( @interactive : $interactive:literal, $v:ident : ( $( $rest:tt )* ) ) => {
        let $v = $crate::scan!(@interactive: $interactive, @expandtuple, ( $( $rest )* ));
    };
    // let $v: $t = ......
    ( @interactive : $interactive:literal, $v:ident : $t:ty ) => {
        let $v = $crate::iolib::scan_string($interactive).parse::<$t>().unwrap();
    };
    // let $v: $t = ......, .......
    ( @interactive : $interactive:literal, $v:ident : $t:ty, $( $rest:tt )+ ) => {
        $crate::scan!(@interactive: $interactive, $v : $t);
        $crate::scan!(@interactive: $interactive, $( $rest )+);
    };
    // ......
    ( $( $rest:tt )* ) => {
        $crate::scan!(@interactive: false, $( $rest )*);
    };
}

#[macro_export]
macro_rules! scani {
    ( $( $rest:tt )* ) => {
        $crate::scan!(@interactive: true, $( $rest )*);
    };
}
}


mod modint {
    pub struct MontgomeryOperator {
        pub modulo: u64,
        pub inv_modulo: u64,
        pub r: u64,
        pub neg_r: u64,
        pub half_modulo: u64,
        pub r2: u64,
        pub d: u64
    }
    
    impl MontgomeryOperator {
        pub const fn new(modulo: u64) -> Self {
            assert!(modulo & 1 != 0);
    
            let inv_modulo = {
                let mut i = 0;
                let mut inv_modulo = modulo;
                while i < 5 {
                    inv_modulo = inv_modulo.wrapping_mul(2u64.wrapping_sub(modulo.wrapping_mul(inv_modulo)));
                    i += 1;
                }
                inv_modulo
            };
    
            let half_modulo = (modulo >> 1) + 1;
            let r = modulo.wrapping_neg() % modulo;
            let neg_r = modulo - r;
            let r2 = ((modulo as u128).wrapping_neg() % (modulo as u128)) as u64;
            let d = (modulo-1) >> (modulo-1).trailing_zeros();
    
            Self { modulo, inv_modulo, r, neg_r, half_modulo, r2, d }
        }
    
        pub const fn add(&self, a: u64, b: u64) -> u64 {
            let (t, fa) = a.overflowing_add(b);
            let (u, fs) = t.overflowing_sub(self.modulo);
            if fa || !fs { u } else { t }
        }
    
        pub const fn sub(&self, a: u64, b: u64) -> u64 {
            let (t, f) = a.overflowing_sub(b);
            if f { t.wrapping_add(self.modulo) } else { t }
        }
    
        pub const fn div2(&self, ar: u64) -> u64 {
            if ar & 1 != 0 {
                (ar >> 1) + self.half_modulo
            } else {
                ar >> 1
            }
        }
    
        pub const fn mul(&self, ar: u64, br: u64) -> u64 {
            let t = (ar as u128) * (br as u128);
            let (t, f) = ((t >> 64) as u64).overflowing_sub((((((t as u64).wrapping_mul(self.inv_modulo)) as u128) * self.modulo as u128) >> 64) as u64);
            if f { t.wrapping_add(self.modulo) } else { t }
        }
    
        pub const fn mr(&self, ar: u64) -> u64 {
            let (t, f) = (((((ar.wrapping_mul(self.inv_modulo)) as u128) * (self.modulo as u128)) >> 64) as u64).overflowing_neg();
            if f { t.wrapping_add(self.modulo) } else { t }
        }
        pub const fn ar(&self, a: u64) -> u64 {
            self.mul(a, self.r2)
        }
    
        pub const fn pow(&self, mut ar: u64, mut b: u64) -> u64 {
            let mut t = if (b & 1) != 0 { ar } else { self.r };
            b >>= 1;
            while b != 0 {
                ar = self.mul(ar, ar);
                if b & 1 != 0 { t = self.mul(t, ar); }
                b >>= 1;
            }
            t
        }
    }
}
