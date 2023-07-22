use std::ffi::c_void;
extern "C" {
    pub fn mmap(
        addr: *mut c_void,
        length: usize,
        prot: i32,
        flags: i32,
        fd: i32,
        offset: i64,
    ) -> *mut c_void;
}

pub const PROT_READ: i32 = 1;
pub const MAP_PRIVATE: i32 = 2;
