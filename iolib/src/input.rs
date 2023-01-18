use std::io::{BufRead, Read, StdinLock};
use std::ptr::copy_nonoverlapping;
use std::slice::from_raw_parts_mut;

const BUF_SIZE: usize = 1 << 18;

pub struct FastInput {
    head: usize,
    tail: usize,
    interactive: bool,
    eof: bool,
    buf: [u8; BUF_SIZE],
}

impl FastInput {
    pub const fn new() -> Self {
        Self {
            head: 0,
            tail: 0,
            interactive: false,
            eof: false,
            buf: [0; 1 << 18],
        }
    }

    #[inline]
    pub fn set_interactive(&mut self) { self.interactive = true; }

    #[inline]
    unsafe fn load(&mut self) {
        // BUF: [buf_head............head....tail...]
        let buf_head = self.buf.as_mut_ptr();
        // src = buf_head + head
        // so, src = &head
        let src = buf_head.add(self.head);
        let count = self.tail - self.head;
        // <before>
        // BUF: [buf_head............[head....tail]...]
        //          ^        copy       |
        //          |___________________|
        // <after>
        // BUF: [[head....tail].............[head....tail]...]
        copy_nonoverlapping(src, buf_head, count);
        // let buf = from_raw_parts_mut(buf_head.add(count), BUF_SIZE - count);
        // self.tail = count + STDIN_SOURCE().read(buf).unwrap();
        self.tail = count
            + if !self.interactive {
                let buf = from_raw_parts_mut(buf_head.add(count), BUF_SIZE - count);
                let res = STDIN_SOURCE().read(buf).unwrap();
                self.eof |= res == 0;
                res
            } else {
                let mut buf = vec![];
                let res = STDIN_SOURCE().read_until(b'\n', &mut buf).unwrap();
                copy_nonoverlapping(buf.as_ptr(), buf_head.add(count), res);
                res
            };
        self.head = 0;
        if self.tail < BUF_SIZE {
            self.buf[self.tail] = b' ';
        }
    }

    #[inline]
    fn readc(&mut self) -> u8 {
        let res = self.buf[self.head];
        self.head += 1;
        res
    }

    #[inline(always)]
    fn refill_buffer(&mut self) {
        if self.eof {
            return;
        }
        if !self.interactive && self.head + 32 > self.tail {
            unsafe { self.load() }
        } else if self.interactive && self.head >= self.tail {
            unsafe { self.load() }
        }
    }

    #[inline]
    pub fn read_u64(&mut self) -> u64 {
        self.refill_buffer();

        let mut x = 0u64;
        while !self.buf[self.head].is_ascii_whitespace() {
            x = x * 10 + (self.buf[self.head] - b'0') as u64;
            self.head += 1;
        }
        self.head += 1;
        x
    }

    #[inline]
    pub fn read_i64(&mut self) -> i64 {
        self.refill_buffer();

        if self.buf[self.head] == b'-' {
            self.head += 1;
            -(self.read_u64() as i64)
        } else {
            self.read_u64() as i64
        }
    }

    #[inline]
    pub fn read_char(&mut self) -> char {
        self.refill_buffer();

        let c = self.readc();
        if self.buf[self.head].is_ascii_whitespace() {
            self.head += 1;
        }

        c as char
    }

    #[inline]
    pub fn read_string(&mut self) -> String {
        if self.interactive {
            let mut buf = String::new();
            std::io::BufReader::read_line(&mut std::io::BufReader::new(unsafe { STDIN_SOURCE() }), &mut buf).unwrap();
            return buf;
        }

        self.refill_buffer();

        let mut tail = self.head;
        while tail < self.tail && !self.buf[tail].is_ascii_whitespace() {
            tail += 1;
        }

        let mut res = String::from_utf8_lossy(&self.buf[self.head..tail]).into_owned();

        self.head = tail;

        if tail == self.tail {
            res.push_str(&self.read_string());
        } else {
            self.head += 1;
        }

        res
    }
}

macro_rules! impl_read_signed_integeer {
    ( $( { $t:ty, $fname:ident } )* ) => {
        $(impl FastInput {
            #[inline]
            pub fn $fname(&mut self) -> $t { self.read_i64() as $t }
        })*
    };
}

macro_rules! impl_read_unsigned_integeer {
    ( $( { $t:ty, $fname:ident } )* ) => {
        $(impl FastInput {
            #[inline]
            pub fn $fname (&mut self) -> $t { self.read_u64() as $t }
        })*
    };
}

impl_read_signed_integeer!({i8, read_i8} {i16, read_i16} {i32, read_i32} {i128, read_i128} {isize, read_isize});
impl_read_unsigned_integeer!({u8, read_u8} {u16, read_u16} {u32, read_u32} {u128, read_u128} {usize, read_usize});

fn init() -> &'static mut StdinLock<'static> {
    let stdin = Box::leak(Box::new(std::io::stdin()));
    unsafe {
        STDIN = Box::leak(Box::new(stdin.lock()));
        STDIN_SOURCE = get_stdin_source
    }

    get_stdin_source()
}

#[inline(always)]
fn get_stdin_source() -> &'static mut StdinLock<'static> { unsafe { STDIN.as_mut().unwrap() } }

static mut INPUT: FastInput = FastInput::new();
static mut STDIN: *mut StdinLock<'static> = 0 as *mut StdinLock<'static>;
static mut STDIN_SOURCE: fn() -> &'static mut StdinLock<'static> = init;

pub fn get_input() -> &'static mut FastInput { unsafe { &mut INPUT } }
pub fn set_interactive() { unsafe { INPUT.set_interactive() } }
