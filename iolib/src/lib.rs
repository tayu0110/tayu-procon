mod input;

pub use input::{get_input, set_interactive};

#[macro_export]
macro_rules! scan {
    // Terminator
    ( $(, )? ) => {};
    // Vec<Vec<....>>, ......
    ( $v: ident : [ [ $( $inner:tt )+ ] ; $len:expr ] $(, $( $rest:tt )* )? ) => {
        let $v = (0..$len).map(|_| { $crate::scan!(w: [ $( $inner )+ ]); w }).collect::<Vec<_>>();
        $( $crate::scan!($( $rest )*); )?
    };
    // Vec<$t>, .....
    ( $v:ident : [ $t:tt ; $len:expr ] $(, $( $rest:tt )* )? ) => {
        let $v = (0..$len).map(|_| { $crate::scan!($v : $t); $v }).collect::<Vec<_>>();
        $( $crate::scan!($( $rest )*); )?
    };
    // Expand tuple
    ( @expandtuple, ( $t:tt )) => {
        { $crate::scan!(w: $t); w }
    };
    // Expand tuple
    ( @expandtuple, ( $t:tt $(, $rest:tt )* ) ) => {
        (
            $crate::scan!(@expandtuple, ( $t ))
            $(, $crate::scan!(@expandtuple, ( $rest )) )*
        )
    };
    // let $v: ($t, $u, ....) = (.......)
    ( $v:ident : ( $( $rest:tt )* ) ) => {
        let $v = $crate::scan!(@expandtuple, ( $( $rest )* ));
    };
    // let $v: $t = ......, .......
    ( $v:ident : $t:tt $(, $( $rest:tt )* )? ) => {
        $crate::read_value!($v : $t);
        $( $crate::scan!($( $rest )*); )?
    };
    // ......
    ( $( $rest:tt )* ) => {
        $crate::scan!($( $rest )*);
    };
}

#[macro_export]
macro_rules! scani {
    ( $( $rest:tt )* ) => {
        $crate::set_interactive();
        $crate::scan!( $( $rest )* );
    };
}

#[macro_export]
macro_rules! read_value {
    ( $v:ident : i8 ) => { let $v = $crate::get_input().read_i8(); };
    ( $v:ident : i16 ) => { let $v = $crate::get_input().read_i16(); };
    ( $v:ident : i32 ) => { let $v = $crate::get_input().read_i32(); };
    ( $v:ident : i64 ) => { let $v = $crate::get_input().read_i64(); };
    ( $v:ident : i128 ) => { let $v = $crate::get_input().read_i128(); };
    ( $v:ident : isize ) => { let $v = $crate::get_input().read_isize(); };
    ( $v:ident : u8 ) => { let $v = $crate::get_input().read_u8(); };
    ( $v:ident : u16 ) => { let $v = $crate::get_input().read_u16(); };
    ( $v:ident : u32 ) => { let $v = $crate::get_input().read_u32(); };
    ( $v:ident : u64 ) => { let $v = $crate::get_input().read_u64(); };
    ( $v:ident : u128 ) => { let $v = $crate::get_input().read_u128(); };
    ( $v:ident : usize ) => { let $v = $crate::get_input().read_usize(); };
    ( $v:ident : char ) => { let $v = $crate::get_input().read_char(); };
    ( $v:ident : String ) => { let $v = $crate::get_input().read_string(); };
    ( $v:ident : $t:ty ) => { let $v: $t = $crate::get_input().read_string().parse().unwrap(); };
}
