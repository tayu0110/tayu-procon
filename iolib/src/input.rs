use std::io::{BufRead, Read, StdinLock};
use std::ptr::copy_nonoverlapping;

const BUF_SIZE: usize = 1 << 18;

pub trait Readable {
    fn read(src: &mut FastInput) -> Self;
}

impl Readable for char {
    fn read(src: &mut FastInput) -> Self { src.read_char() }
}

impl Readable for String {
    fn read(src: &mut FastInput) -> Self { src.read_string() }
}

macro_rules! impl_readable_integer {
    ( $( { $t:ty, $ut:ty } )* ) => {
        $(impl Readable for $ut {
            fn read(src: &mut FastInput) -> $ut {
                src.load();
                let mut x = 0 as $ut;
                while !src.peek().is_ascii_whitespace() {
                    x = x * 10 + (src.next() - b'0') as $ut;
                }
                src.next();
                x
            }
        }
        impl Readable for $t {
            fn read(src: &mut FastInput) -> $t {
                src.load();
                if src.peek() == b'-' {
                    src.next();
                    - (<$ut>::read(src) as $t)
                } else {
                    <$ut>::read(src) as $t
                }
            }
        })*
    };
}

impl_readable_integer!({i8, u8} {i16, u16} {i32, u32} {i64, u64} {i128, u128} {isize, usize});

macro_rules! impl_readable_float {
    ( $( $t:ty )* ) => {
        $(impl Readable for $t {
            fn read(src: &mut FastInput) -> $t { src.read_string().parse().unwrap() }
        })*
    };
}

impl_readable_float!(f32 f64);

struct InputSource<'a> {
    uninit: bool,
    source: *mut StdinLock<'a>,
}

impl<'a> InputSource<'a> {
    pub const fn new() -> Self { Self { uninit: true, source: 0 as *mut StdinLock<'a> } }

    #[inline]
    fn init(&mut self) {
        let stdin = Box::leak::<'a>(Box::new(std::io::stdin()));
        self.source = Box::leak::<'a>(Box::new(stdin.lock()));
    }

    #[inline]
    pub fn get(&mut self) -> &mut StdinLock<'a> {
        if self.uninit {
            self.init();
            self.uninit = false;
        }
        unsafe { self.source.as_mut().unwrap() }
    }

    #[allow(dead_code)]
    #[inline]
    pub fn read_until_newline(&mut self, buf: &mut Vec<u8>) -> Result<usize, std::io::Error> { self.get().read_until(b'\n', buf) }
}

pub struct FastInput<'a> {
    head: usize,
    tail: usize,
    eof: bool,
    buf: [u8; BUF_SIZE],
    source: InputSource<'a>,
}

impl<'a> FastInput<'a> {
    pub const fn new() -> Self {
        Self {
            head: 0,
            tail: 0,
            eof: false,
            buf: [0; BUF_SIZE],
            source: InputSource::new(),
        }
    }

    #[inline]
    fn load(&mut self) {
        if !self.eof && self.head + 32 > self.tail {
            let count = self.tail - self.head;
            unsafe { copy_nonoverlapping(self.buf[self.head..self.tail].as_ptr(), self.buf.as_mut_ptr(), count) }
            let res = self.source.get().read(&mut self.buf[count..]).unwrap();
            self.eof |= res == 0;
            self.tail = count + res;
            self.head = 0;
            if self.tail < BUF_SIZE {
                self.buf[self.tail] = b' ';
            }
        }
    }

    #[inline]
    fn peek(&self) -> u8 { self.buf[self.head] }

    #[inline]
    fn next(&mut self) -> u8 {
        let res = self.buf[self.head];
        self.head += 1;
        res
    }

    #[inline]
    pub fn read<R: Readable>(&mut self) -> R { R::read(self) }

    #[inline]
    pub fn read_char(&mut self) -> char {
        self.load();

        let c = self.next();
        if self.peek().is_ascii_whitespace() {
            self.next();
        }

        c as char
    }

    #[inline]
    pub fn read_string(&mut self) -> String {
        self.load();

        let mut tail = self.head;
        while tail < self.tail && !self.buf[tail].is_ascii_whitespace() {
            tail += 1;
        }

        let mut res = String::from_utf8_lossy(&self.buf[self.head..tail]).into_owned();

        self.head = tail;
        if tail == self.tail && !self.eof {
            res.push_str(&self.read_string());
        } else {
            self.head += 1;
        }

        res
    }
}

static mut INPUT: FastInput = FastInput::new();

#[inline]
pub fn get_input() -> &'static mut FastInput<'static> { unsafe { &mut INPUT } }
