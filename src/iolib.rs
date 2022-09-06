use std::cell::RefCell;
use std::collections::VecDeque;
use std::io::{
    Read, BufRead, Error
};
use std::thread_local;

thread_local! {
    static BUF: RefCell<VecDeque<String>> = RefCell::new(VecDeque::new())
}

fn refill_buffer(interactive: bool) -> Result<(), Error> {
    let mut s = String::new();
    
    if cfg!(debug_assertions) || interactive {
        std::io::stdin().lock().read_line(&mut s)?;
    } else {
        std::io::stdin().lock().read_to_string(&mut s)?;
    }

    BUF.with(|buf| {
        buf.borrow_mut().append(&mut s.split_ascii_whitespace().map(|s| s.to_string()).collect());
        Ok(())
    })
}

pub fn scan_string(interactive: bool) -> String {
    BUF.with(|buf| {
        if buf.borrow().is_empty() {
            refill_buffer(interactive).unwrap();
        }

        if let Some(s) = buf.borrow_mut().pop_front() {
            return s;
        }

        unreachable!("Read Error: No input items.");
    })
}

#[macro_export]
macro_rules! scan {
    ( interactive : $interactive:literal ) => {};
    ( interactive : $interactive:literal, ) => {};
    ( interactive : $interactive:literal, $v:ident : [ $t:ty ; $len:expr ]) => {
        let $v = {
            let len = $len;
            (0..len).map(|_| { $crate::scan!(interactive: $interactive, $v : $t); $v }).collect::<Vec<_>>()
        };
    };
    ( interactive : $interactive:literal, $v:ident : [ $t:ty ; $len:expr ], $( $rest:tt )+ ) => {
        $crate::scan!(interactive: $interactive, $v : [ $t ; $len ]);
        $crate::scan!(interactive: $interactive, $( $rest )+);
    };
    ( interactive : $interactive:literal, $v:ident : $t:ty ) => {
        let $v = $crate::iolib::scan_string($interactive).parse::<$t>().unwrap();
    };
    ( interactive : $interactive:literal, $v:ident : $t:ty, $( $rest:tt )+ ) => {
        scan!(interactive: $interactive, $v : $t);
        scan!(interactive: $interactive, $( $rest )+);
    };
    // ( $( $v:ident : $t:ty ),* ) => {
    //     scan!(interactive: false, $( $v : $t ),*);
    // };
    ( $( $rest:tt )+ ) => {
        $crate::scan!(interactive: false, $( $rest )+);
    };

}

#[macro_export]
macro_rules! scani {
    ( $( $v:ident : $t:ty ),* ) => {
        $crate::scan!(interactive: true, $( $v : $t ),*);
    };
}
