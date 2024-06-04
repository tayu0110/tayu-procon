use std::{
    cell::RefCell,
    io::Write,
    iter,
    ptr::{addr_of_mut, write_volatile},
};

const LUT: [u8; 40000] = {
    let mut cnt = 0;
    let mut lut = [0; 40000];

    while cnt < 10000 {
        let th = cnt / 1000;
        let hu = cnt / 100 % 10;
        let te = cnt / 10 % 10;
        let on = cnt % 10;
        lut[cnt * 4] = th as u8 + b'0';
        lut[cnt * 4 + 1] = hu as u8 + b'0';
        lut[cnt * 4 + 2] = te as u8 + b'0';
        lut[cnt * 4 + 3] = on as u8 + b'0';
        cnt += 1;
    }
    lut
};

pub trait Display {
    fn fmt(&self, buf: &mut Buffer, sep: &str);
}

#[inline(always)]
fn write_small_integer(int: u16, buf: &mut Buffer) {
    debug_assert!(int < 10000);
    let base = int as usize * 4;
    buf.write_unchecked(&LUT[base + 3 - int.ilog10() as usize..base + 4]);
}

macro_rules! impl_stringify_unsigned_integer {
    ( $t:ty $( as $convert:ty )?, $st:ty, $block:literal ) => {
        impl Display for $t {
            fn fmt(&self, f: &mut Buffer, _: &str) {
                f.reserve($block * 4);
                let mut now = *self $( as $convert )?;
                if now == 0 {
                    f.write_unchecked("0".as_bytes());
                    return;
                }
                if now < 10000 {
                    write_small_integer(now as u16, f);
                    return;
                }
                let mut t = [0; $block];
                let mut cnt = $block;
                while now >= 10000 {
                    cnt -= 1;
                    (now, t[cnt]) = (now / 10000, (now % 10000) as u16);
                }
                write_small_integer(now as u16, f);
                for &t in &t[cnt..] {
                    let t = t as usize;
                    f.write_unchecked(&LUT[t * 4..t * 4 + 4]);
                }
            }
        }

        impl Display for $st {
            fn fmt(&self, buf: &mut Buffer, sep: &str) {
                if *self < 0 {
                    buf.write("-".as_bytes());
                    self.unsigned_abs().fmt(buf, sep);
                } else {
                    (*self as $t).fmt(buf, sep);
                }
            }
        }
    };
}
impl_stringify_unsigned_integer!(u8 as u32, i8, 0);
impl_stringify_unsigned_integer!(u16 as u32, i16, 2);
impl_stringify_unsigned_integer!(u32, i32, 3);
impl_stringify_unsigned_integer!(u64, i64, 5);
impl_stringify_unsigned_integer!(usize, isize, 5);
impl_stringify_unsigned_integer!(u128, i128, 10);

impl Display for char {
    fn fmt(&self, buf: &mut Buffer, _: &str) {
        let mut b = [0; 4];
        buf.write(self.encode_utf8(&mut b).as_bytes());
    }
}

impl Display for str {
    fn fmt(&self, buf: &mut Buffer, _: &str) {
        buf.write(self.as_bytes());
    }
}

impl<T: Display> Display for [T] {
    fn fmt(&self, buf: &mut Buffer, sep: &str) {
        if let Some(item) = self.first() {
            item.fmt(buf, sep);
            for item in self.iter().skip(1) {
                buf.write(sep.as_bytes());
                item.fmt(buf, sep);
            }
        }
    }
}

macro_rules! impl_base_ust {
    ( $ty:ty, $b:ty, $( $t:tt )* ) => {
        impl<$( $t )*> Display for $ty {
            fn fmt(&self, buf: &mut Buffer, sep: &str) {
                <$b as Display>::fmt(self, buf, sep)
            }
        }
    };
}
impl_base_ust!(&str, str,);
impl_base_ust!(String, str,);
impl_base_ust!(&[T], [T], T: Display);
impl_base_ust!([T; N], [T], T: Display, const N: usize);
impl_base_ust!(Vec<T>, [T], T: Display);

macro_rules! impl_fmt_iterator {
    ( $t:ty, $( $g:tt )* ) => {
        impl<$( $g )*> Display for $t {
            fn fmt(&self, buf: &mut Buffer, sep: &str) {
                let mut iter = self.clone();
                if let Some(item) = iter.next() {
                    item.fmt(buf, sep);
                    for item in iter {
                        buf.write(sep.as_bytes());
                        item.fmt(buf, sep);
                    }
                }
            }
        }
    };
}

impl_fmt_iterator!(std::slice::Iter<'_, T>, T: Display);
impl_fmt_iterator!(iter::Chain<A, B>, T: Display, A: Clone + Iterator<Item = T>, B: Clone + Iterator<Item = T>);
impl_fmt_iterator!(iter::Cloned<I>, 'a, T: Display + Clone + 'a, I: Clone + Iterator<Item = &'a T>);
impl_fmt_iterator!(iter::Copied<I>, 'a, T: Display + Clone + Copy + 'a, I: Clone + Iterator<Item = &'a T>);
impl_fmt_iterator!(iter::Cycle<I>, T: Display, I: Clone + Iterator<Item = T>);
impl_fmt_iterator!(iter::Filter<I, P>, T: Display, I: Clone + Iterator<Item = T>, P: Clone + FnMut(&I::Item) -> bool);
impl_fmt_iterator!(iter::FilterMap<I, F>, T: Display, I: Clone + Iterator, F: Clone + FnMut(I::Item) -> Option<T>);
impl_fmt_iterator!(iter::Map<I, F>, T: Display, I: Clone + Iterator, F: Clone + FnMut(I::Item) -> T);
impl_fmt_iterator!(iter::Skip<I>, T: Display, I: Clone + Iterator<Item = T>);
impl_fmt_iterator!(iter::StepBy<I>, T: Display, I: Clone + Iterator<Item = T>);
impl_fmt_iterator!(iter::Take<I>, T: Display, I: Clone + Iterator<Item = T>);

pub struct Buffer {
    head: usize,
    buf: [u8; Self::LEN],
}

impl Buffer {
    const LEN: usize = 1 << 20;

    const fn new() -> Self {
        Self { head: 0, buf: [0; Self::LEN] }
    }

    fn reserve(&mut self, len: usize) {
        assert!(len <= Self::LEN);
        if self.head + len > Self::LEN {
            self.flush();
        }
    }

    fn write_unchecked(&mut self, buf: &[u8]) {
        self.buf[self.head..self.head + buf.len()].copy_from_slice(buf);
        self.head += buf.len();
    }

    fn write(&mut self, buf: &[u8]) {
        if self.head + buf.len() <= Self::LEN {
            self.write_unchecked(buf);
            return;
        }
        for c in buf.chunks(Self::LEN) {
            self.flush();
            self.buf[..c.len()].copy_from_slice(c);
            self.head = c.len();
        }
    }

    fn flush(&mut self) {
        if self.head > 0 {
            std::io::stdout().write_all(&self.buf[..self.head]).ok();
            self.head = 0;
        }
    }
}

struct DumFlush(u32);
impl Drop for DumFlush {
    fn drop(&mut self) {
        get_output().flush();
    }
}

thread_local! {
    static DUMMY: RefCell<DumFlush> = const { RefCell::new(DumFlush(0)) };
}

static mut BUFFER: Buffer = Buffer::new();
static mut GET_BUFFER: fn() -> &'static mut Buffer = init;
#[cold]
fn init() -> &'static mut Buffer {
    DUMMY.with(|d| unsafe { write_volatile(addr_of_mut!(d.borrow_mut().0), 32) });
    unsafe { GET_BUFFER = get_output }
    get_output()
}
fn get_output() -> &'static mut Buffer {
    unsafe { addr_of_mut!(BUFFER).as_mut().unwrap() }
}
pub fn get_buffer() -> &'static mut Buffer {
    unsafe { GET_BUFFER() }
}
