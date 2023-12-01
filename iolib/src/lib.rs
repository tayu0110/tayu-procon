// The original source of the scan macro is statiolake/proconio-rs!
// Please refer to there for the implementation!
mod ext;
mod input;
mod output;
mod parse_number;

pub use input::{get_stdin_source, FastInput, Readable};
pub use output::get_output_source;

#[macro_export]
macro_rules! read_value {
    (@kind [[$($kind:tt)*]]) => {
        $crate::read_value!(@array @kind [] @rest $($kind)*)
    };
    (@array @kind [$($kind:tt)*] @rest ; $($rest:tt)*) => {
        $crate::read_value!(@array @kind [$($kind)*] @len $($rest)*)
    };
    (@array @kind [$($kind:tt)*] @rest $t:tt $($rest:tt)*) => {
        $crate::read_value!(@array @kind [$($kind)* $t] @rest $($rest)*)
    };
    (@array @kind [$($kind:tt)*] @len $($len:tt)*) => {{
        let len = $($len)*;
        (0..len).map(|_| $crate::read_value!(@kind [$($kind)*])).collect::<Vec<_>>()
    }};

    (@kind [($($kind:tt)*)]) => {
        $crate::read_value!(@tuple @kind [] @current [] @rest $($kind)*)
    };
    (@tuple @kind [$([$($kind:tt)*])*] @current [] @rest) => {
        (
            $($crate::read_value!(@kind [$($kind)*]),)*
        )
    };
    (@tuple @kind [$([$($kind:tt)*])*] @current [$($current:tt)*] @rest) => {
        $crate::read_value!(@tuple @kind [$([$($kind)*])* [$($current)*]] @current [] @rest)
    };
    (@tuple @kind [$([$($kind:tt)*])*] @current [$($current:tt)*] @rest , $($rest:tt)*) => {
        $crate::read_value!(@tuple @kind [$([$($kind)*])* [$($current)*]] @current [] @rest $($rest)*)
    };
    (@tuple @kind [$([$($kind:tt)*])*] @current [$($current:tt)*] @rest $t:tt $($rest:tt)*) => {
        $crate::read_value!(@tuple @kind [$([$($kind)*])*] @current [$($current)* $t] @rest $($rest)*)
    };

    (@kind [$t:tt]) => {
        $crate::get_stdin_source().read::<$t>()
    };
}

#[macro_export]
macro_rules! scan {
    ( @rest ) => {};

    ( @rest mut $($rest:tt)* ) => {
        $crate::scan!([mut] @rest $($rest)*)
    };
    ( @rest $($rest:tt)* ) => {
        $crate::scan!([] @rest $($rest)*)
    };

    ( [$($mut:tt)?] @rest $var:tt : $($rest:tt)* ) => {
        $crate::scan!(
            [$($mut)*]
            @var $var
            @kind []
            @rest $($rest)*
        );
    };

    ( [$($mut:tt)?] @var $var:tt @kind [$($kind:tt)*] @rest ) => {
        let $($mut)* $var = $crate::read_value!(@kind [$($kind)*]);
    };
    ( [$($mut:tt)?] @var $var:tt @kind [$($kind:tt)*] @rest , $($rest:tt)* ) => {
        $crate::scan!([$($mut)*] @var $var @kind [$($kind)*] @rest);
        $crate::scan!(@rest $($rest)*);
    };
    ( [$($mut:tt)?] @var $var:tt @kind [$($kind:tt)*] @rest $t:tt $($rest:tt)* ) => {
        $crate::scan!([$($mut)*] @var $var @kind [$($kind)* $t] @rest $($rest)*);
    };

    ($($rest:tt)*) => {
        $crate::scan!(@rest $($rest)*);
    };
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
    ( $t:expr, sep=$delim:expr) => {
        $crate::get_output_source().store_vec(&$t, $delim);
    };
    ( $t:expr ) => {
        $crate::putv!($t, sep='\n');
    };
}

#[macro_export]
macro_rules! putvln {
    ( $t:expr, sep=$delim:expr) => {
        $crate::putv!($t, sep=$delim);
        $crate::putln!();
    };
    ( $t: expr ) => {
        $crate::putvln!($t, sep='\n');
    };
}
