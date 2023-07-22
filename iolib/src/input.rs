use super::ext::{mmap, MAP_PRIVATE, PROT_READ};
use super::parse_number::{parse16c, parse8c, parse8lec};
use std::fs::File;
use std::io::Read;
use std::os::unix::io::FromRawFd;
use std::ptr::{null_mut, slice_from_raw_parts_mut};

pub trait Readable {
    fn read(src: &mut FastInput) -> Self;
}

impl Readable for char {
    fn read(src: &mut FastInput) -> Self {
        src.read_char()
    }
}

impl Readable for String {
    fn read(src: &mut FastInput) -> Self {
        src.read_string()
    }
}

macro_rules! impl_readable_integer {
    ( $( { $t:ty, $ut:ty } )* ) => {
        $(impl Readable for $ut {
            #[inline]
            fn read(src: &mut FastInput) -> $ut {
                src.read_u64() as $ut
            }
        }
        impl Readable for $t {
            #[inline]
            fn read(src: &mut FastInput) -> $t {
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

pub struct FastInput {
    head: usize,
    _file: File,
    buf: Box<[u8]>,
}

impl FastInput {
    fn new(file: File, buf: Box<[u8]>) -> Self {
        Self {
            head: 0,
            _file: file,
            buf,
        }
    }

    #[inline]
    fn peek(&self) -> u8 {
        self.buf[self.head]
    }

    #[inline]
    fn next(&mut self) -> Option<u8> {
        if self.head == self.buf.len() {
            None
        } else {
            self.head += 1;
            Some(self.buf[self.head - 1])
        }
    }

    #[inline]
    pub fn read<R: Readable>(&mut self) -> R {
        R::read(self)
    }

    #[inline]
    pub fn read_char(&mut self) -> char {
        while let Some(c) = self.next() {
            if !c.is_ascii_whitespace() {
                return c as char;
            }
        }
        unreachable!(
            "Error: buffer is empty. line: {}, file: {}",
            line!(),
            file!()
        )
    }

    #[inline]
    pub fn read_u64(&mut self) -> u64 {
        let mut tail = self.head;
        while tail < self.buf.len() && !self.buf[tail].is_ascii_whitespace() {
            tail += 1;
        }

        let offset = tail - self.head;
        let res = if offset < 8 {
            unsafe { parse8lec(&self.buf[self.head..self.head + 8], offset as u8) }
        } else if offset == 8 {
            unsafe { parse8c(&self.buf[self.head..self.head + 8]) }
        } else if offset < 16 {
            let rem = offset - 8;
            let upper = unsafe { parse8lec(&self.buf[self.head..self.head + 8], rem as u8) };
            let lower = unsafe { parse8c(&self.buf[self.head + rem..self.head + offset]) };
            upper * 10000_0000 + lower
        } else if offset == 16 {
            unsafe { parse16c(&self.buf[self.head..self.head + 16]) }
        } else {
            let rem = offset - 16;
            let upper = unsafe { parse8lec(&self.buf[self.head..self.head + 8], rem as u8) };
            let lower = unsafe { parse16c(&self.buf[self.head + rem..self.head + offset]) };
            upper * 10000_0000_0000_0000 + lower
        };
        self.head = tail + 1;
        res
    }

    #[inline]
    pub fn read_string(&mut self) -> String {
        let mut tail = self.head;
        while tail < self.buf.len() && !self.buf[tail].is_ascii_whitespace() {
            tail += 1;
        }

        let res = String::from_utf8_lossy(&self.buf[self.head..tail]).into_owned();
        self.head = tail + 1;
        res
    }
}

static mut INPUT: *mut FastInput = 0 as *mut FastInput;
static mut STDINT_SOURCE: fn() -> &'static mut FastInput = init;

#[inline]
fn init() -> &'static mut FastInput {
    let mut stdin = unsafe { File::from_raw_fd(0) };
    let meta = stdin.metadata().unwrap();
    let buf = if meta.is_file() {
        let len = meta.len() as usize + 32;
        let mapping = unsafe { mmap(null_mut() as _, len, PROT_READ, MAP_PRIVATE, 0, 0) };
        let res = slice_from_raw_parts_mut(mapping as *mut u8, len);
        unsafe { Box::from_raw(res) }
    } else {
        let mut buf = Vec::with_capacity(1 << 18);
        stdin.read_to_end(&mut buf).unwrap();
        buf.resize(buf.len() + 32, b' ');
        buf.into_boxed_slice()
    };

    let input = FastInput::new(stdin, buf);
    unsafe {
        INPUT = Box::leak(Box::new(input));
        STDINT_SOURCE = get_input;
    }
    get_input()
}

#[inline]
fn get_input() -> &'static mut FastInput {
    unsafe { INPUT.as_mut().unwrap_unchecked() }
}

#[inline]
pub fn get_stdin_source() -> &'static mut FastInput {
    unsafe { STDINT_SOURCE() }
}
