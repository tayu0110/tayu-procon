use std::io::{BufRead, BufReader, Error, Read, StdinLock};
use std::str::SplitWhitespace;

static mut BUFFERED_STDIN: *mut BufReader<StdinLock<'static>> = 0 as *mut BufReader<StdinLock<'static>>;
static mut BUF_SPLIT_WHITESPACE: *mut SplitWhitespace<'static> = 0 as *mut SplitWhitespace<'static>;

#[inline]
fn refill_buffer(interactive: bool) -> Result<(), Error> {
    let mut s = String::new();

    unsafe {
        if BUFFERED_STDIN == 0 as *mut BufReader<StdinLock> {
            let stdin = Box::leak(Box::new(std::io::stdin()));
            BUFFERED_STDIN = Box::leak(Box::new(BufReader::new(stdin.lock())));
        }

        if cfg!(debug_assertions) || interactive {
            (*BUFFERED_STDIN).read_line(&mut s)?;
        } else {
            (*BUFFERED_STDIN).read_to_string(&mut s)?;
        }

        BUF_SPLIT_WHITESPACE = Box::leak(Box::new(Box::leak(s.into_boxed_str()).split_whitespace()));
        Ok(())
    }
}

#[inline]
pub fn scan_string(interactive: bool) -> &'static str {
    unsafe {
        if BUF_SPLIT_WHITESPACE == 0 as *mut SplitWhitespace<'static> {
            refill_buffer(interactive).unwrap();

            return (*BUF_SPLIT_WHITESPACE).next().unwrap();
        }

        if let Some(s) = (*BUF_SPLIT_WHITESPACE).next() {
            return s;
        }

        refill_buffer(interactive).unwrap();

        (*BUF_SPLIT_WHITESPACE).next().expect("Read Error: No input item.")
    }
}

#[macro_export]
macro_rules! scan {
    // Terminator
    ( @interactive : $interactive:literal $(, )? ) => {};
    // Vec<Vec<....>>, ......
    ( @interactive : $interactive:literal, $v: ident : [ [ $( $inner:tt )+ ] ; $len:expr ] $(, $( $rest:tt )* )? ) => {
        let $v = (0..$len).map(|_| { $crate::scan!(@interactive: $interactive, w: [ $( $inner )+ ]); w }).collect::<Vec<_>>();
        $( $crate::scan!(@interactive: $interactive, $( $rest )*); )?
    };
    // Vec<$t>, .....
    ( @interactive : $interactive:literal, $v:ident : [ $t:tt ; $len:expr ] $(, $( $rest:tt )*)? ) => {
        let $v = (0..$len).map(|_| { $crate::scan!(@interactive: $interactive, $v : $t); $v }).collect::<Vec<_>>();
        $( $crate::scan!(@interactive: $interactive, $( $rest )*); )?
    };
    // Expand tuple
    ( @interactive : $interactive:literal, @expandtuple, ( $t:tt )) => {
        { $crate::scan_string($interactive).parse::<$t>().unwrap() }
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
    // let $v: $t = ......, .......
    ( @interactive : $interactive:literal, $v:ident : $t:ty $(, $( $rest:tt )* )? ) => {
        let $v = $crate::scan_string($interactive).parse::<$t>().unwrap();
        $( $crate::scan!(@interactive: $interactive, $( $rest )*); )?
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
