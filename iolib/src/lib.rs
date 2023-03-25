mod input;
mod output;

pub use input::{get_input, FastInput, Readable};
pub use output::OUTPUT;

#[macro_export]
macro_rules! scan {
    // Terminator
    ( $(, )? ) => {};
    // Vec<Vec<....>>, ......
    ( $v: ident : [ [ $( $inner:tt )+ ] ; $len:expr ] $(, $( $rest:tt )* )? ) => { let $v = (0..$len).map(|_| { $crate::scan!(w: [ $( $inner )+ ]); w }).collect::<Vec<_>>(); $( $crate::scan!($( $rest )*); )? };
    // Vec<$t>, .....
    ( $v:ident : [ $t:tt ; $len:expr ] $(, $( $rest:tt )* )? ) => { let $v = (0..$len).map(|_| { $crate::scan!($v : $t); $v }).collect::<Vec<_>>(); $( $crate::scan!($( $rest )*); )? };
    // Expand tuple
    ( @expandtuple, ( $t:tt )) => { { $crate::scan!(w: $t); w } };
    // Expand tuple
    ( @expandtuple, ( $t:tt $(, $rest:tt )* ) ) => { ( $crate::scan!(@expandtuple, ( $t )) $(, $crate::scan!(@expandtuple, ( $rest )) )* ) };
    // let $v: ($t, $u, ....) = (.......)
    ( $v:ident : ( $( $rest:tt )* ) ) => { let $v = $crate::scan!(@expandtuple, ( $( $rest )* )); };
    // let $v: $t = ......, .......
    ( $v:ident : $t:tt $(, $( $rest:tt )* )? ) => { let $v: $t = $crate::get_input().read::<$t>(); $( $crate::scan!($( $rest )*); )? };
    // ......
    ( $( $rest:tt )* ) => { $crate::scan!($( $rest )*); };
}

#[macro_export]
macro_rules! put {
    () => {};
    ( $t:expr ) => { $crate::OUTPUT.with(|o| o.borrow_mut().write($t)); };
    ( $t:expr $(, $rest:tt )* ) => { $crate::put!($t); $crate::put!(' '); $crate::put!($( $rest )*); };
}

#[macro_export]
macro_rules! putln {
    () => { $crate::put!('\n'); };
    ( $t:expr ) => { $crate::put!($t); $crate::put!('\n'); };
    ( $t:expr $(, $rest:tt )* ) => { $crate::put!($t); $crate::put!(' '); $crate::put!($( $rest )*); $crate::put!('\n'); };
}

#[macro_export]
macro_rules! putvec_with_space {
    ( $t:expr ) => { $crate::OUTPUT.with(|o| o.borrow_mut().store_vec(&$t, ' ')); };
}

#[macro_export]
macro_rules! putvec_with_spaceln {
    ( $t:expr ) => { $crate::putvec_with_space!($t); $crate::putln!(); };
}
