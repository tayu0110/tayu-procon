use std::{
    cell::RefCell,
    io::{StdoutLock, Write},
    ptr::copy_nonoverlapping,
};
const BUF_SIZE: usize = 1 << 20;

pub trait Writable {
    fn write(&self, dest: &mut FastOutput);
}

impl Writable for char {
    fn write(&self, dest: &mut FastOutput) {
        dest.store_byte(*self as u8)
    }
}

impl Writable for String {
    fn write(&self, dest: &mut FastOutput) {
        dest.store_string(self)
    }
}

impl Writable for str {
    fn write(&self, dest: &mut FastOutput) {
        dest.store_string(self)
    }
}

impl Writable for &str {
    fn write(&self, dest: &mut FastOutput) {
        dest.store_string(self)
    }
}

const LUT: [u8; 40000] = {
    let mut lut = [0; 40000];
    let mut i = 0;
    while i < 10000 {
        lut[i * 4] = (i / 1000) as u8 + b'0';
        lut[i * 4 + 1] = (i % 1000 / 100) as u8 + b'0';
        lut[i * 4 + 2] = (i % 100 / 10) as u8 + b'0';
        lut[i * 4 + 3] = (i % 10) as u8 + b'0';
        i += 1;
    }
    lut
};

macro_rules! impl_writable_integer {
    ($( {$t:ty, $ut:ty, $size:expr} )*) => {
        $(impl Writable for $ut {
            fn write(&self, dest: &mut FastOutput) {
                if self == &0 {
                    dest.store_byte(b'0');
                    return;
                }

                let mut keep = [0u16; $size];
                let mut head = 0;
                let mut now = *self as u64;
                while now >= 10000_0000 {
                    let rem = now % 10000_0000;
                    let upper = rem / 10000;
                    let lower = rem % 10000;
                    keep[head] = lower as u16;
                    keep[head+1] = upper as u16;
                    head += 2;
                    now /= 10000_0000;
                }

                if now >= 10000 {
                    let rem = now % 10000;
                    keep[head] = rem as u16;
                    head += 1;
                    now /= 10000;
                }

                let now = now as u16;
                let log = now.ilog10() as usize;
                let buf = dest.borrow_buffer((head << 2) + log + 1);
                if log == 0 {
                    buf[0] = now as u8 + b'0';
                } else {
                    let n = (now as usize) * 4 + 3 - log;
                    buf[..log+1].copy_from_slice(&LUT[n..n+log+1]);
                }

                let mut cursor = log+1;
                while head > 0 {
                    head -= 1;
                    let n = keep[head] as usize * 4;
                    buf[cursor..cursor+4].copy_from_slice(&LUT[n..n+4]);
                    cursor += 4;
                }
            }
        }
        impl Writable for $t {
            fn write(&self, dest: &mut FastOutput) {
                if self < &0 {
                    '-'.write(dest);
                }
                (self.abs() as $ut).write(dest);
            }
        })*
    };
}

impl_writable_integer!({i8, u8, 1} {i16, u16, 2} {i32, u32, 3} {i64, u64, 5} {i128, u128, 10} {isize, usize, 5});

macro_rules! impl_writable_float {
    ($( $t:ty )*) => {
        $(impl Writable for $t {
            fn write(&self, dest: &mut FastOutput) {
                format!("{}", self).write(dest)
            }
        })*
    };
}

impl_writable_float!(f32 f64);
impl<T: Clone + Writable> Writable for Vec<T> {
    fn write(&self, dest: &mut FastOutput) {
        dest.store_vec(self, '\n')
    }
}

pub struct FastOutput<'a> {
    tail: usize,
    buf: [u8; BUF_SIZE],
    dest: *mut StdoutLock<'a>,
}
impl<'a> FastOutput<'a> {
    #[inline]
    pub const fn new() -> Self {
        Self { tail: 0, buf: [0; BUF_SIZE], dest: 0 as *mut StdoutLock<'a> }
    }
    #[inline]
    fn init(&mut self) {
        let stdout = Box::leak::<'a>(Box::new(std::io::stdout()));
        self.dest = Box::leak::<'a>(Box::new(stdout.lock()));
    }
    #[inline]
    pub fn flush(&mut self) {
        unsafe {
            self.dest
                .as_mut()
                .unwrap_unchecked()
                .write_all(&self.buf[..self.tail])
                .unwrap_unchecked();
        }
        self.tail = 0;
    }
    pub fn borrow_buffer(&mut self, size: usize) -> &mut [u8] {
        if BUF_SIZE - self.tail <= size {
            self.flush();
        }
        self.tail += size;
        &mut self.buf[self.tail - size..self.tail]
    }
    #[inline]
    pub fn store(&mut self, bytes: &[u8]) {
        if bytes.len() < BUF_SIZE - self.tail {
            unsafe {
                copy_nonoverlapping(
                    bytes.as_ptr(),
                    self.buf[self.tail..].as_mut_ptr(),
                    bytes.len(),
                )
            }
            self.tail += bytes.len();
            return;
        }
        let head = BUF_SIZE - self.tail;
        unsafe {
            copy_nonoverlapping(
                bytes[..head].as_ptr(),
                self.buf[self.tail..].as_mut_ptr(),
                head,
            )
        }
        self.tail = BUF_SIZE;
        self.flush();
        bytes[head..].chunks(BUF_SIZE).for_each(|v| {
            self.tail = if v.len() < BUF_SIZE { v.len() } else { BUF_SIZE };
            unsafe { copy_nonoverlapping(v.as_ptr(), self.buf[0..].as_mut_ptr(), v.len()) }
            if v.len() == BUF_SIZE {
                self.flush()
            }
        });
    }
    #[inline]
    pub fn store_byte(&mut self, b: u8) {
        self.buf[self.tail] = b;
        self.tail += 1;
        if self.tail == BUF_SIZE {
            self.flush();
        }
    }
    #[inline]
    pub fn store_string(&mut self, s: &str) {
        let bytes = s.as_bytes();
        self.store(bytes);
    }
    #[inline]
    pub fn write<T: Writable>(&mut self, data: T) {
        data.write(self)
    }
    #[inline]
    pub fn store_vec<T: Clone + Writable>(&mut self, v: &Vec<T>, delim: char) {
        if v.is_empty() {
            return;
        }
        v[0].clone().write(self);
        for v in v.iter().skip(1) {
            delim.write(self);
            v.clone().write(self);
        }
    }

    #[inline]
    pub fn store_iter<I: Iterator<Item = T>, T: Writable>(&mut self, mut iter: I, delim: char) {
        if let Some(n) = iter.next() {
            n.write(self);
        }

        for n in iter {
            delim.write(self);
            n.write(self);
        }
    }
}
struct DummyForFlush(u32);
impl Drop for DummyForFlush {
    fn drop(&mut self) {
        unsafe {
            OUTPUT.flush();
        }
    }
}
static mut OUTPUT: FastOutput<'static> = FastOutput::new();
static mut STDOUTSOURCE: fn() -> &'static mut FastOutput<'static> = init;
thread_local! {static DUMMY:RefCell<DummyForFlush> =RefCell::new(DummyForFlush(0));}
fn init() -> &'static mut FastOutput<'static> {
    DUMMY.with(|d| {
        unsafe { core::ptr::write_volatile((&mut d.borrow_mut().0) as *const _ as *mut _, 32) };
    });
    unsafe {
        STDOUTSOURCE = get_output;
    }
    let res = get_output();
    res.init();
    res
}
fn get_output() -> &'static mut FastOutput<'static> {
    unsafe { &mut OUTPUT }
}
pub fn get_output_source() -> &'static mut FastOutput<'static> {
    unsafe { STDOUTSOURCE() }
}
