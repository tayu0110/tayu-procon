#[cfg(target_family = "unix")]
mod ext;
mod input;
mod output;
mod parse_number;

pub use input::{get_stdin_source, FromBytes, Source};
pub use output::{get_buffer, Display};

#[macro_export]
macro_rules! scan {
    ( @src $src:ident, @mut[$( $mut:tt )?], @id[$v:ident], @ty[$( $ty:tt )*], @rest $(, $( $rest:tt )* )? ) => {
        $crate::read_value!(@src $src, @mut[$( $mut )?], @id[$v], @ty[$( $ty )*]);
        $crate::scan!(@src $src, $( $( $rest )* )?);
    };
    ( @src $src:ident, @mut[$( $mut:tt )?], @id[$v:ident], @ty[$( $ty:tt )*], @rest $t:tt $( $rest:tt )* ) => {
        $crate::scan!(@src $src, @mut[$( $mut )?], @id[$v], @ty[$( $ty )* $t], @rest $( $rest )*);
    };
    ( @src $src:ident, @mut[$( $mut:tt )?], @rest $v:ident : $( $t:tt )* ) => {
        $crate::scan!(@src $src, @mut[$( $mut )?], @id[$v], @ty[], @rest $( $t )*);
    };
    ( @src $src:ident, @mut[], @rest mut $( $t:tt )* ) => {
        $crate::scan!(@src $src, @mut[mut], @rest $( $t )*);
    };
    ( @src $src:ident, $( $t:tt )+ ) => {
        $crate::scan!(@src $src, @mut[], @rest $( $t )+);
    };
    ( @src $src:ident, ) => {
    };
    ( $( $t:tt )+ ) => {
        let mut __cpio_source_lock_object = $crate::get_stdin_source();
        $crate::scan!(@src __cpio_source_lock_object, $( $t )+);
    };
    () => {
        ::std::compile_error!("Failed to parse macro");
    }
}

#[macro_export]
macro_rules! read_value {
    ( @src $src:ident, @mut[$( $mut:tt )?], @id[$v:ident], @ty[$( $t:tt )*]) => {
        let $( $mut )? $v = unsafe { $crate::read_value!(@src $src, @ty[$( $t )*]) };
    };

    // array or Vec
    ( @src $src:ident, @ty[ [$( $t:tt )*] ] ) => {
        $crate::read_value!(@arr @src $src, @ty[], @rest $( $t )*)
    };
    ( @arr @src $src:ident, @ty[$( $ty:tt )*], @rest ; const $( $len:tt )* ) => {{
        const LEN: usize = ( $( $len )* );
        let mut arr = [$crate::read_value!(@src $src, @ty[$( $ty )*]); LEN];
        for i in 1..LEN { arr[i] = $crate::read_value!(@src $src, @ty[$( $ty )*]); }
        arr
    }};
    ( @arr @src $src:ident, @ty[$( $ty:tt )*], @rest ; $( $len:tt )*) => {{
        let len = ( $($len)* );
        let mut res = Vec::with_capacity(len);
        res.extend((0..len).map(|_| $crate::read_value!(@src $src, @ty[$( $ty )*])));
        res
    }};
    ( @arr @src $src:ident, @ty[$( $ty:tt )*], @rest $t:tt $( $rest:tt )* ) => {
        $crate::read_value!(@arr @src $src, @ty[$( $ty )* $t], @rest $( $rest )*)
    };

    // tuple
    ( @src $src:ident, @ty[( $( $t:tt )* )]) => {
        $crate::read_value!(@tup @src $src, @ty[], @cur[], @rest $( $t )*);
    };
    ( @tup @src $src:ident, @ty [$([$($ty:tt)*])*], @cur [], @rest) => {
        ( $($crate::read_value!(@src $src, @ty [$($ty)*]),)* )
    };
    ( @tup @src $src:ident, @ty [$([$($ty:tt)*])*], @cur [$($cur:tt)*], @rest) => {
        $crate::read_value!(@tup @src $src, @ty [$([$($ty)*])* [$($cur)*]], @cur [], @rest)
    };
    ( @tup @src $src:ident, @ty [$([$($ty:tt)*])*], @cur [$($cur:tt)*], @rest , $($rest:tt)*) => {
        $crate::read_value!(@tup @src $src, @ty [$([$($ty)*])* [$($cur)*]], @cur [], @rest $($rest)*)
    };
    ( @tup @src $src:ident, @ty [$([$($ty:tt)*])*], @cur [$($cur:tt)*], @rest $t:tt $($rest:tt)*) => {
        $crate::read_value!(@tup @src $src, @ty[$([$($ty)*])*], @cur [$($cur)* $t], @rest $($rest)*)
    };

    ( @src $src:ident, @ty[ $t:ty ] ) => {{
        let token = $src.next_token();
        <$t as $crate::FromBytes>::from_bytes(token)
    }};
    ( @src $src:ident, @ty[] ) => {
        ::std::compile_error!("Failed to parse macro");
    };
}

#[macro_export]
macro_rules! put {
    ( $arg:expr, $( $args:expr ),* , @sep = $sep:expr) => {
        $crate::put!($arg);
        $crate::put!(@tail, $( $args ),* , @sep = $sep);
    };
    ( @tail, $( $args:expr ),* , @sep = $sep:expr) => {
        $(
            $crate::Display::fmt(& $sep, $crate::get_buffer(), "");
            $crate::Display::fmt(& $args, $crate::get_buffer(), "");
        )*
    };
    ( $arg:expr ) => {
        $crate::Display::fmt(& $arg, $crate::get_buffer(), "");
    };
    ( $( $args:expr ),* ) => {
        $crate::put!($( $args ),* , @sep = "\n");
    };
    () => {}
}

#[macro_export]
macro_rules! putln {
    ( $( $args:expr ),+ , @sep = $sep:expr) => {
        $crate::put!($( $args ),+ , @sep = $sep);
        $crate::putln!();
    };
    ( $( $args:expr ),+ ) => {
        $crate::put!($( $args ),+);
        $crate::putln!();
    };
    () => {
        $crate::put!("\n");
    }
}
