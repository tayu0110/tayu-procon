use std::{fs::File, io::Read, str::from_utf8};

use crate::parse_number::{parse16c, parse4c, parse8c};

#[inline(always)]
const fn parse_small_integer(bytes: &[u8], d: usize) -> u64 {
    const S: u64 = b'0' as u64 * 11;
    const T: u64 = b'0' as u64 * 111;
    debug_assert!(0 < d && d < 4);
    match d {
        1 => (bytes[0] & 15) as u64,
        2 => bytes[0] as u64 * 10 + bytes[1] as u64 - S,
        3 => bytes[0] as u64 * 100 + bytes[1] as u64 * 10 + bytes[2] as u64 - T,
        _ => unreachable!(),
    }
}

pub trait FromBytes {
    fn from_bytes(bytes: &[u8]) -> Self;
}

impl FromBytes for u64 {
    fn from_bytes(bytes: &[u8]) -> Self {
        debug_assert!(!bytes.is_empty() && bytes.len() <= 20);
        const TEN: [u64; 4] = [1, 10, 100, 1000];
        unsafe {
            match bytes.len() {
                1 => parse_small_integer(bytes, 1),
                2 => parse_small_integer(bytes, 2),
                3 => parse_small_integer(bytes, 3),
                4 => parse4c(bytes.try_into().unwrap()),
                8 => parse8c(bytes.try_into().unwrap()),
                12 => {
                    parse4c(bytes[..4].try_into().unwrap()) * 100_000_000
                        + parse8c(bytes[4..].try_into().unwrap())
                }
                16 => parse16c(bytes),
                20 => {
                    parse16c(bytes[..16].try_into().unwrap()) * 10_000
                        + parse4c(bytes[16..].try_into().unwrap())
                }
                len => {
                    let offset = len & !0b11;
                    Self::from_bytes(&bytes[..offset]) * TEN[len & 0b11]
                        + parse_small_integer(&bytes[offset..], len & 0b11)
                }
            }
        }
    }
}

macro_rules! impl_unsigned_integer_from_bytes {
    ( $( $t:ty ),* ) => {
        $(
            impl FromBytes for $t {
                fn from_bytes(bytes: &[u8]) -> Self {
                    <u64 as FromBytes>::from_bytes(bytes) as $t
                }
            }
        )*
    };
}
impl_unsigned_integer_from_bytes!(u8, u16, u32, usize);

impl FromBytes for u128 {
    fn from_bytes(bytes: &[u8]) -> Self {
        if bytes.len() > 19 {
            const P: u128 = 10u128.pow(19);
            let offset = bytes.len() - 19;
            u64::from_bytes(&bytes[..offset]) as u128 * P
                + u64::from_bytes(&bytes[offset..]) as u128
        } else {
            u64::from_bytes(bytes) as u128
        }
    }
}

macro_rules! impl_signed_integer_from_bytes {
    ( $( $s:ty, $u:ty ),* ) => {
        $(
            impl FromBytes for $s {
                fn from_bytes(bytes: &[u8]) -> Self {
                    debug_assert!(!bytes.is_empty());
                    let sgn = bytes[0] == b'-';
                    let mut res = <$u as FromBytes>::from_bytes(&bytes[sgn as usize..]);
                    debug_assert!(res <= <$s>::MAX as $u + sgn as $u);
                    if sgn { res = res.wrapping_neg(); }
                    res as $s
                }
            }
        )*
    };
}
impl_signed_integer_from_bytes!(i8, u8, i16, u16, i32, u32, i64, u64, isize, usize, i128, u128);

impl FromBytes for char {
    fn from_bytes(bytes: &[u8]) -> Self {
        debug_assert!(!bytes.is_empty());
        let mut it = from_utf8(bytes)
            .expect("Malformed UTF-8 byte sequence")
            .chars();
        let res = it.next().unwrap();
        assert!(
            it.next().is_none(),
            "Failed to parse `char`: multiple characters"
        );
        res
    }
}

impl FromBytes for String {
    fn from_bytes(bytes: &[u8]) -> Self {
        from_utf8(bytes)
            .expect("Malformed UTF-8 byte sequence")
            .to_owned()
    }
}

pub struct Source {
    buf: Box<[u8]>,
    // This `File` is required.
    // Without it, stdin will be closed and input will not be possible.
    _file: Option<File>,
    head: usize,
}

impl Source {
    fn get_buffer_use_std(stdin: &mut impl Read) -> Box<[u8]> {
        let mut buf = Vec::with_capacity(1 << 18);
        stdin.read_to_end(&mut buf).unwrap();
        buf.resize(buf.len() + 32, b' ');
        buf.into_boxed_slice()
    }

    #[cfg(target_family = "unix")]
    pub fn new() -> Self {
        use std::{
            os::fd::FromRawFd,
            ptr::{null_mut, slice_from_raw_parts_mut},
        };

        use crate::ext::{mmap, MAP_PRIVATE, PROT_READ};

        let mut stdin = unsafe { File::from_raw_fd(0) };
        let meta = stdin.metadata().unwrap();
        let buf = if meta.is_file() {
            let len = meta.len() as usize;
            let mapping = unsafe { mmap(null_mut() as _, len, PROT_READ, MAP_PRIVATE, 0, 0) };
            let res = slice_from_raw_parts_mut(mapping as *mut u8, len);
            unsafe { Box::from_raw(res) }
        } else {
            Self::get_buffer_use_std(&mut stdin)
        };

        Self {
            buf,
            _file: Some(stdin),
            head: 0,
        }
    }

    #[cfg(not(target_family = "unix"))]
    pub fn new() -> Self {
        let buf = Self::get_buffer_use_std(&mut std::io::stdin().lock());
        Self {
            buf,
            _file: None,
            head: 0,
        }
    }

    pub fn next_start(&mut self) -> Option<usize> {
        while self.buf.get(self.head)? <= &b' ' {
            self.head += 1;
        }
        Some(self.head)
    }

    pub fn next_token(&mut self) -> &[u8] {
        let head = self.next_start().expect("There are no more tokens");
        while self.buf.get(self.head).filter(|&&b| b > b' ').is_some() {
            self.head += 1;
        }
        &self.buf[head..self.head]
    }
}

static mut INPUT: *mut Source = 0 as *mut Source;
static mut STDIN_SOURCE: fn() -> &'static mut Source = init;

#[cold]
fn init() -> &'static mut Source {
    unsafe {
        INPUT = Box::leak(Box::new(Source::new()));
        STDIN_SOURCE = || INPUT.as_mut().unwrap_unchecked();
        STDIN_SOURCE()
    }
}

pub fn get_stdin_source() -> &'static mut Source {
    unsafe { STDIN_SOURCE() }
}
