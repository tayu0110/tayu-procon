#[cfg(target_family = "unix")]
use super::ext::{mmap, MAP_PRIVATE, PROT_READ};
use super::parse_number::{parse16c, parse4c, parse4lec, parse8c, parse8lec};
use ds::FixedRingQueue;
#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{__m256i, _mm256_cmpgt_epi8, _mm256_loadu_si256, _mm256_movemask_epi8};
use std::fs::File;
use std::io::Read;
use std::mem::transmute;
#[cfg(target_family = "unix")]
use std::os::unix::io::FromRawFd;
#[cfg(target_family = "unix")]
use std::ptr::{null_mut, slice_from_raw_parts_mut};

fn parse_u64(buf: &[u8]) -> u64 {
    let offset = buf.len();
    unsafe {
        if offset < 8 {
            buf.iter()
                .fold(0u32, |s, &v| s * 10 + v as u32 - b'0' as u32) as u64
        } else if offset == 8 {
            parse8c(buf.try_into().unwrap_unchecked())
        } else if offset == 12 {
            let upper = parse4c(buf[..4].try_into().unwrap_unchecked());
            let lower = parse8c(buf[4..].try_into().unwrap_unchecked());
            upper * 100_000_000 + lower
        } else if offset < 16 {
            let rem = offset - 8;
            let upper = parse8lec(buf[..8].try_into().unwrap_unchecked(), rem as u8);
            let lower = parse8c(buf[rem..].try_into().unwrap_unchecked());
            upper * 100_000_000 + lower
        } else if offset == 16 {
            parse16c(buf)
        } else if offset == 20 {
            let upper = buf[..4]
                .iter()
                .fold(0u32, |s, &v| s * 10 + v as u32 - b'0' as u32) as u64;
            let lower = parse16c(&buf[4..]);
            upper * 10_000_000_000_000_000 + lower
        } else {
            let rem = offset - 16;
            let upper = parse4lec(buf[..4].try_into().unwrap_unchecked(), rem as u8);
            let lower = parse16c(&buf[rem..]);
            upper * 10_000_000_000_000_000 + lower
        }
    }
}

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
    ( $( { $t:ty, $ut:ty } ),* ) => {
        $(impl Readable for $ut {
            #[inline]
            fn read(src: &mut FastInput) -> $ut {
                let buf = src.source.next();
                parse_u64(buf) as $ut
            }
        }
        impl Readable for $t {
            #[inline]
            fn read(src: &mut FastInput) -> $t {
                let buf = src.source.next();
                if buf[0] == b'-' {
                    - (parse_u64(&buf[1..]) as $t)
                } else {
                    parse_u64(buf) as $t
                }
            }
        })*
    };
}

impl_readable_integer!({i8, u8}, {i16, u16}, {i32, u32}, {i64, u64}, {i128, u128}, {isize, usize});

macro_rules! impl_readable_float {
    ( $( $t:ty )* ) => {
        $(impl Readable for $t {
            fn read(src: &mut FastInput) -> $t { src.read_string().parse().unwrap() }
        })*
    };
}

impl_readable_float!(f32 f64);

pub struct FastInput {
    source: Source,
}

impl FastInput {
    pub fn new() -> Self {
        Self { source: Source::new() }
    }

    #[inline]
    pub fn read<R: Readable>(&mut self) -> R {
        R::read(self)
    }

    #[inline]
    pub fn read_char(&mut self) -> char {
        let c = self.source.next();
        assert_eq!(c.len(), 1);
        char::from_u32(c[0] as u32).unwrap()
    }

    #[inline]
    pub fn read_string(&mut self) -> String {
        unsafe { String::from_utf8_unchecked(self.source.next().to_vec()) }
    }
}

static mut INPUT: *mut FastInput = 0 as *mut FastInput;
static mut STDIN_SOURCE: fn() -> &'static mut FastInput = init;

#[inline]
fn init() -> &'static mut FastInput {
    unsafe {
        INPUT = Box::leak(Box::new(FastInput::new()));
        STDIN_SOURCE = get_input;
    }
    get_input()
}

#[inline]
fn get_input() -> &'static mut FastInput {
    unsafe { INPUT.as_mut().unwrap_unchecked() }
}
#[inline]
pub fn get_stdin_source() -> &'static mut FastInput {
    unsafe { STDIN_SOURCE() }
}

struct Source {
    head: usize,
    next: Option<usize>,
    _file: Option<File>,
    len: usize,
    buf: Box<[u8]>,
    queue: FixedRingQueue<(usize, usize), { 1 << 4 }>,
}

impl Source {
    // Since Ascii Code use up to 0x20 as control codes, characters smaller than 0x21 are identified as control codes.
    const SEPARATORS: __m256i = unsafe { transmute([0x21i8; 32]) };

    #[cfg(target_family = "unix")]
    fn new() -> Self {
        let mut stdin = unsafe { File::from_raw_fd(0) };
        let meta = stdin.metadata().unwrap();
        let (buf, len) = if meta.is_file() {
            let len = meta.len() as usize + 32;
            let mapping = unsafe { mmap(null_mut() as _, len, PROT_READ, MAP_PRIVATE, 0, 0) };
            let res = slice_from_raw_parts_mut(mapping as *mut u8, len);
            (unsafe { Box::from_raw(res) }, meta.len() as usize)
        } else {
            let mut buf = Vec::with_capacity(1 << 18);
            stdin.read_to_end(&mut buf).unwrap();
            let len = buf.len();
            buf.resize(buf.len() + 32, b' ');
            (buf.into_boxed_slice(), len)
        };

        Self {
            head: 0,
            next: None,
            _file: Some(stdin),
            len,
            buf,
            queue: FixedRingQueue::<(usize, usize), { 1 << 4 }>::new(),
        }
    }

    #[cfg(not(target_family = "unix"))]
    fn new() -> Self {
        let mut buf = Vec::with_capacity(1 << 18);
        std::io::stdin().lock().read_to_end(&mut buf).ok();
        let len = buf.len();
        buf.resize(buf.len() + 32, b' ');
        Self {
            head: 0,
            next: None,
            _file: None,
            len,
            buf: buf.into_boxed_slice(),
            queue: FixedRingQueue::<(usize, usize), { 1 << 4 }>::new(),
        }
    }

    fn next(&mut self) -> &[u8] {
        if let Some((head, tail)) = self.queue.pop() {
            return &self.buf[head..tail];
        }

        let (head, tail) = unsafe { self.fill() };
        &self.buf[head..tail]
    }

    #[target_feature(enable = "avx2")]
    unsafe fn fill(&mut self) -> (usize, usize) {
        let mut head = usize::MAX;
        if let Some(next) = self.next {
            head = next;
            self.next = None;
        }

        while self.queue.is_empty() && self.head + 32 <= self.len {
            let bytes = _mm256_loadu_si256(self.buf[self.head..].as_ptr() as _);
            // The byte determined to be a control code is 0xFF.
            let gt = _mm256_cmpgt_epi8(Self::SEPARATORS, bytes);

            let mut b = _mm256_movemask_epi8(gt) as u32;
            let mut now = self.head;
            if b == 0 && head == usize::MAX {
                head = self.head;
            }
            if head != usize::MAX && b == u32::MAX {
                b = 0;
            }
            while b > 0 {
                if head == usize::MAX {
                    let tr = b.trailing_ones();
                    b >>= tr;
                    now += tr as usize;
                    head = now;
                } else {
                    let tr = b.trailing_zeros();
                    b >>= tr;
                    now += tr as usize;
                    self.queue.push((head, now));
                    head = usize::MAX;
                }
            }

            self.head += 32;
        }

        if self.queue.is_empty() {
            if head == usize::MAX {
                while self.buf[self.head].is_ascii_whitespace() {
                    self.head += 1;
                }
                head = self.head;
            }
            while self.head < self.len && !self.buf[self.head].is_ascii_whitespace() {
                self.head += 1;
            }
            self.queue.push((head, self.head));
            head = usize::MAX;
        }

        if head < usize::MAX {
            self.next = Some(head);
        }

        self.queue.pop_unchecked()
    }
}
