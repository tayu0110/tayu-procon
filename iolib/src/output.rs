use std::{
    cell::RefCell,
    io::{StdoutLock, Write},
    ptr::copy_nonoverlapping,
};
const BUF_SIZE: usize = 1 << 15;

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

const LUT: &'static [u8; 3000] = b"000001002003004005006007008009010011012013014015016017018019020021022023024025026027028029030031032033034035036037038039040041042043044045046047048049050051052053054055056057058059060061062063064065066067068069070071072073074075076077078079080081082083084085086087088089090091092093094095096097098099100101102103104105106107108109110111112113114115116117118119120121122123124125126127128129130131132133134135136137138139140141142143144145146147148149150151152153154155156157158159160161162163164165166167168169170171172173174175176177178179180181182183184185186187188189190191192193194195196197198199200201202203204205206207208209210211212213214215216217218219220221222223224225226227228229230231232233234235236237238239240241242243244245246247248249250251252253254255256257258259260261262263264265266267268269270271272273274275276277278279280281282283284285286287288289290291292293294295296297298299300301302303304305306307308309310311312313314315316317318319320321322323324325326327328329330331332333334335336337338339340341342343344345346347348349350351352353354355356357358359360361362363364365366367368369370371372373374375376377378379380381382383384385386387388389390391392393394395396397398399400401402403404405406407408409410411412413414415416417418419420421422423424425426427428429430431432433434435436437438439440441442443444445446447448449450451452453454455456457458459460461462463464465466467468469470471472473474475476477478479480481482483484485486487488489490491492493494495496497498499500501502503504505506507508509510511512513514515516517518519520521522523524525526527528529530531532533534535536537538539540541542543544545546547548549550551552553554555556557558559560561562563564565566567568569570571572573574575576577578579580581582583584585586587588589590591592593594595596597598599600601602603604605606607608609610611612613614615616617618619620621622623624625626627628629630631632633634635636637638639640641642643644645646647648649650651652653654655656657658659660661662663664665666667668669670671672673674675676677678679680681682683684685686687688689690691692693694695696697698699700701702703704705706707708709710711712713714715716717718719720721722723724725726727728729730731732733734735736737738739740741742743744745746747748749750751752753754755756757758759760761762763764765766767768769770771772773774775776777778779780781782783784785786787788789790791792793794795796797798799800801802803804805806807808809810811812813814815816817818819820821822823824825826827828829830831832833834835836837838839840841842843844845846847848849850851852853854855856857858859860861862863864865866867868869870871872873874875876877878879880881882883884885886887888889890891892893894895896897898899900901902903904905906907908909910911912913914915916917918919920921922923924925926927928929930931932933934935936937938939940941942943944945946947948949950951952953954955956957958959960961962963964965966967968969970971972973974975976977978979980981982983984985986987988989990991992993994995996997998999";

impl Writable for u8 {
    fn write(&self, dest: &mut FastOutput) {
        if self == &0 {
            dest.store_byte(b'0');
            return;
        }
        let mut head = 4;
        let mut buf = [0u8; 4];
        let mut now = *self;
        if now >= 100 {
            let rem = (now as usize % 100) << 1;
            head -= 2;
            buf[head..head + 2].copy_from_slice(&LUT[rem..rem + 2]);
            now /= 100;
        }
        if now >= 10 {
            head -= 2;
            let n = (now as usize) << 1;
            buf[head..head + 2].copy_from_slice(&LUT[n..n + 2]);
        } else {
            head -= 1;
            buf[head] = now as u8 + b'0';
        }
        dest.store(&buf[head..]);
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
                let mut now = *self as u64;
                while now >= 1000_000 {
                    let rem = (now % 1000_000) as usize;
                    let upper = (rem / 1000) * 3;
                    let lower = (rem % 1000) * 3;
                    head -= 6;
                    buf[head..head+3].copy_from_slice(&LUT[upper..upper+3]);
                    buf[head+3..head+6].copy_from_slice(&LUT[lower..lower+3]);
                    now /= 1000_000;
                }
                if now >= 1000 {
                    let rem = (now as usize % 1000) * 3;
                    head -= 3;
                    buf[head..head+3].copy_from_slice(&LUT[rem..rem+3]);
                    now /= 1000;
                }
                if now >= 100 {
                    head -= 3;
                    let n = (now as usize) * 3;
                    buf[head..head+3].copy_from_slice(&LUT[n..n+3]);
                } else if now >= 10 {
                    head -= 2;
                    let n = (now as usize) * 3 + 1;
                    buf[head..head+2].copy_from_slice(&LUT[n..n+2]);
                } else {
                    head -= 1;
                    buf[head] = now as u8 + b'0';
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

pub struct FastOutput<'a> {
    tail: usize,
    buf: [u8; BUF_SIZE],
    dest: *mut StdoutLock<'a>,
}
impl<'a> FastOutput<'a> {
    #[inline]
    pub const fn new() -> Self { Self { tail: 0, buf: [0; BUF_SIZE], dest: 0 as *mut StdoutLock<'a> } }
    #[inline]
    fn init(&mut self) {
        let stdout = Box::leak::<'a>(Box::new(std::io::stdout()));
        self.dest = Box::leak::<'a>(Box::new(stdout.lock()));
    }
    #[inline]
    pub fn flush(&mut self) {
        unsafe {
            self.dest.as_mut().unwrap_unchecked().write_all(&self.buf[..self.tail]).unwrap_unchecked();
        }
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
            delim.write(self);
            v.clone().write(self);
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
fn get_output() -> &'static mut FastOutput<'static> { unsafe { &mut OUTPUT } }
pub fn get_output_source() -> &'static mut FastOutput<'static> { unsafe { STDOUTSOURCE() } }
