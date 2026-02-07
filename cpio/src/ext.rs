use std::os::raw::{c_int, c_long, c_void};

unsafe extern "C" {
    pub fn mmap(
        addr: *mut c_void,
        len: usize,
        prot: c_int,
        flags: c_int,
        fd: c_int,
        offset: c_long,
    ) -> *mut c_void;
}

pub const PROT_READ: i32 = 1;
pub const MAP_PRIVATE: i32 = 2;
