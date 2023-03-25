use std::{
    cell::RefCell,
    io::{StdoutLock, Write},
    ptr::copy_nonoverlapping,
};

const BUF_SIZE: usize = 1 << 18;

pub trait Writable {
    fn write(&self, dest: &mut FastOutput);
}

impl Writable for char {
    fn write(&self, dest: &mut FastOutput) { dest.store_byte(*self as u8) }
}

impl Writable for String {
    fn write(&self, dest: &mut FastOutput) { dest.store_string(self) }
}

impl Writable for str {
    fn write(&self, dest: &mut FastOutput) { dest.store_string(self) }
}

impl Writable for &str {
    fn write(&self, dest: &mut FastOutput) { dest.store_string(self) }
}

const TBL: [u8; 40000] = {
    let mut buf = [0; 40000];
    let mut i = 0;
    while i < 10000 {
        buf[i * 4] = (i / 1000) as u8 + b'0';
        buf[i * 4 + 1] = ((i % 1000) / 100) as u8 + b'0';
        buf[i * 4 + 2] = ((i % 100) / 10) as u8 + b'0';
        buf[i * 4 + 3] = (i % 10) as u8 + b'0';
        i += 1;
    }
    buf
};

impl Writable for u8 {
    fn write(&self, dest: &mut FastOutput) {
        if self == &0 {
            dest.store_byte(b'0');
            return;
        }
        let buf = &TBL[*self as usize * 4..*self as usize * 4 + 4];
        for head in 0..4 {
            if buf[head] != b'0' {
                dest.store(&buf[head..]);
                return;
            }
        }
    }
}

impl Writable for i8 {
    fn write(&self, dest: &mut FastOutput) {
        if self < &0 {
            '-'.write(dest);
        }
        (self.abs() as u8).write(dest);
    }
}

macro_rules! impl_writable_integer {
    ($( {$t:ty, $ut:ty, $size:expr} )*) => {
        $(impl Writable for $ut {
            fn write(&self, dest: &mut FastOutput) {
                if self == &0 {
                    dest.store_byte(b'0');
                    return;
                }
                let mut buf = [0; $size];
                let mut head = $size;
                let mut now = *self;
                while now > 0 {
                    head -= 4;
                    let rem = (now % 10000) as usize;
                    buf[head..head+4].copy_from_slice(&TBL[rem*4..rem*4+4]);
                    now /= 10000;
                }
                while buf[head] == b'0' {
                    head += 1;
                }
                dest.store(&buf[head..]);
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

impl_writable_integer!({i16, u16, 8} {i32, u32, 12} {i64, u64, 20} {i128, u128, 40} {isize, usize, 20});

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
    fn write(&self, dest: &mut FastOutput) { dest.store_vec(self, '\n') }
}

struct OutputDestination<'a> {
    uninit: bool,
    dest: *mut StdoutLock<'a>,
}

impl<'a> OutputDestination<'a> {
    #[inline]
    pub const fn new() -> Self { Self { uninit: true, dest: 0 as *mut StdoutLock<'a> } }

    #[inline]
    pub fn init(&mut self) {
        let stdout = Box::leak::<'a>(Box::new(std::io::stdout()));
        self.dest = Box::leak::<'a>(Box::new(stdout.lock()));
    }

    #[inline]
    pub fn get(&mut self) -> &mut StdoutLock<'a> {
        if self.uninit {
            self.init();
            self.uninit = false;
        }
        unsafe { self.dest.as_mut().unwrap() }
    }
}

pub struct FastOutput<'a> {
    tail: usize,
    buf: [u8; BUF_SIZE],
    dest: OutputDestination<'a>,
}

impl<'a> FastOutput<'a> {
    #[inline]
    pub const fn new() -> Self { Self { tail: 0, buf: [0; BUF_SIZE], dest: OutputDestination::new() } }

    #[inline]
    pub fn flush(&mut self) {
        self.dest.get().write_all(&self.buf[..self.tail]).unwrap();
        self.tail = 0;
    }

    #[inline]
    pub fn store(&mut self, bytes: &[u8]) {
        if bytes.len() < BUF_SIZE - self.tail {
            unsafe { copy_nonoverlapping(bytes.as_ptr(), self.buf[self.tail..].as_mut_ptr(), bytes.len()) }
            self.tail += bytes.len();
            return;
        }

        let head = BUF_SIZE - self.tail;
        unsafe { copy_nonoverlapping(bytes[..head].as_ptr(), self.buf[self.tail..].as_mut_ptr(), head) }
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
    pub fn write<T: Writable>(&mut self, data: T) { data.write(self) }

    #[inline]
    pub fn store_vec<T: Clone + Writable>(&mut self, v: &Vec<T>, delim: char) {
        if v.is_empty() {
            return;
        }

        v[0].clone().write(self);
        for v in v.into_iter().skip(1) {
            delim.clone().write(self);
            v.clone().write(self);
        }
    }
}

impl<'a> Drop for FastOutput<'a> {
    fn drop(&mut self) { self.flush(); }
}

thread_local! {
    pub static OUTPUT: RefCell<FastOutput<'static>> = RefCell::new(FastOutput::new());
}
