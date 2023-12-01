mod ext;
mod input;
mod output;
mod parse_number;

pub use input::{get_stdin_source, FastInput, Readable};
pub use output::get_output_source;

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
    ( $v:ident : $t:tt $(, $( $rest:tt )* )? ) => { let $v: $t = $crate::get_stdin_source().read::<$t>(); $( $crate::scan!($( $rest )*); )? };
    // ......
    ( $( $rest:tt )* ) => { $crate::scan!($( $rest )*); };
}

#[macro_export]
macro_rules! put {
    () => {};
    ( $t:expr ) => { $crate::get_output_source().write($t); };
    ( $t:expr $(, $rest:tt )* ) => { $crate::put!($t); $crate::put!(' '); $crate::put!($( $rest )*); };
}

#[macro_export]
macro_rules! putln {
    () => { $crate::put!('\n'); };
    ( $t:expr ) => { $crate::put!($t); $crate::put!('\n'); };
    ( $t:expr $(, $rest:tt )* ) => { $crate::put!($t); $crate::put!(' '); $crate::put!($( $rest )*); $crate::put!('\n'); };
}

#[macro_export]
macro_rules! putv {
    ( $t:expr ) => {
        $crate::get_output_source().store_vec(&$t, '\n');        
    };
}

#[macro_export]
macro_rules! putvln {
    ( $t: expr ) => {
        $crate::putv!($t);
        $crate::putln!();
    };
}

#[macro_export]
macro_rules! putvs {
    ( $t:expr ) => {
        $crate::get_output_source().store_vec(&$t, ' ');
    };
}

#[macro_export]
macro_rules! putvsln {
    ( $t:expr ) => {
        $crate::putvs!($t);
        $crate::putln!();
    };
}

#[macro_export]
macro_rules! putvec_with_space {
    ( $t:expr ) => {
        $crate::get_output_source().store_vec(&$t, ' ');
    };
}

#[macro_export]
macro_rules! putvec_with_spaceln {
    ( $t:expr ) => {
        $crate::putvec_with_space!($t);
        $crate::putln!();
    };
}
