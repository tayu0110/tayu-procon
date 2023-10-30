fn parse4c_core(mut chunk: u32) -> u64 {
    let lower = (chunk & 0x0f000f00) >> 8;
    let upper = (chunk & 0x000f000f) * 10;
    chunk = lower + upper;

    let lower = (chunk & 0x00ff0000) >> 16;
    let upper = (chunk & 0x000000ff) * 100;
    (lower + upper) as u64
}

// This function requests the size of 'buf' must be 4.
// If this condition is not satisfied, the behavior cannot be not defined.
pub(crate) unsafe fn parse4c(buf: [u8; 4]) -> u64 {
    let chunk = u32::from_le_bytes(buf);
    parse4c_core(chunk)
}

pub(crate) unsafe fn parse4lec(buf: [u8; 4], digits: u8) -> u64 {
    let offset = (4 - digits) << 3;
    let chunk = u32::from_le_bytes(buf).wrapping_shl(offset as u32);
    parse4c_core(chunk)
}

fn parse8c_core(mut chunk: u64) -> u64 {
    let lower = (chunk & 0x0f000f000f000f00) >> 8;
    let upper = (chunk & 0x000f000f000f000f) * 10;
    chunk = lower + upper;

    let lower = (chunk & 0x00ff000000ff0000) >> 16;
    let upper = (chunk & 0x000000ff000000ff) * 100;
    chunk = lower + upper;

    let lower = (chunk & 0x0000ffff00000000) >> 32;
    let upper = (chunk & 0x000000000000ffff) * 10000;
    lower + upper
}

// This function requests the size of 'buf' must be 8.
// If this condition is not satisfied, the behavior cannot be not defined.
pub(crate) unsafe fn parse8c(buf: [u8; 8]) -> u64 {
    let chunk = u64::from_le_bytes(buf);
    parse8c_core(chunk)
}

// This function requests the size of 'buf' must be 8.
// In addition, digits must be less than or equal to 8.
// If this condition is not satisfied, the behavior cannot be not defined.
// The 'buf' must be filled with the 0th element in order from the upper digits of the target to be parsed.
// For example, to parse "123", buf[0]='1',buf[1]='2',buf[2]='3'.
pub(crate) unsafe fn parse8lec(buf: [u8; 8], digits: u8) -> u64 {
    // Since little-endian is assumed, the extra digits are present in the upper (8 - 'digits') byte of the chunk.
    // Therefore, by shifting the chunks to the left of the (8 - 'digits') byte, the extra digits can be removed.
    // Example: buf = [0x31, 0x32, 0x33, 0x34, 0x35, 0x36, 0x37, 0x38], digits = 3
    //              -> chunks = 0x3837363534333231, chunks << (8 - 3) * 8 = chunks << 5 * 8 = 0x3332310000000000
    //  If chunks are rewritten to their representation in memory, they are equivalent to [0x00, 0x00, 0x00, 0x00, 0x00, 0x31, 0x32, 0x33] and the upper digits are removed.
    let offset = (8 - digits) << 3;
    let chunk = u64::from_le_bytes(buf).wrapping_shl(offset as u32);
    parse8c_core(chunk)
}

#[cfg(not(target_arch = "x86_64"))]
fn parse16c_core(mut chunk: u128) -> u64 {
    let lower = (chunk & 0x0f000f000f000f000f000f000f000f00) >> 8;
    let upper = (chunk & 0x000f000f000f000f000f000f000f000f) * 10;
    chunk = lower + upper;

    let lower = (chunk & 0x00ff000000ff000000ff000000ff0000) >> 16;
    let upper = (chunk & 0x000000ff000000ff000000ff000000ff) * 100;
    chunk = lower + upper;

    let lower = (chunk & 0x0000ffff000000000000ffff00000000) >> 32;
    let upper = (chunk & 0x000000000000ffff000000000000ffff) * 10000;
    chunk = lower + upper;

    let lower = (chunk >> 64) as u64 & 0x00000000ffffffff;
    let upper = (chunk as u64 & 0x00000000ffffffff) * 10000_0000;
    lower + upper
}

// This function requests the size of 'buf' must be 16.
// If this condition is not satisfied, the behavior cannot be not defined.
#[cfg(not(target_arch = "x86_64"))]
pub(crate) unsafe fn parse16c(buf: &[u8]) -> u64 {
    let buf: [u8; 16] = buf.try_into().unwrap();
    let chunk = u128::from_le_bytes(buf);
    parse16c_core(chunk)
}

// This function requests the size of 'buf' must be 16.
// In addition, digits must be less than or equal to 16.
// If this condition is not satisfied, the behavior cannot be not defined.
// The 'buf' must be filled with the 0th element in order from the upper digits of the target to be parsed.
// For example, to parse "123", buf[0]='1',buf[1]='2',buf[2]='3'.
#[cfg(not(target_arch = "x86_64"))]
pub(crate) unsafe fn parse16lec(buf: &[u8], digits: u8) -> u64 {
    let buf: [u8; 16] = buf.try_into().unwrap();
    let offset = (16 - digits as u32) << 3;
    let chunk = u128::from_le_bytes(buf).wrapping_shl(offset);
    parse16c_core(chunk)
}

#[cfg(target_arch = "x86_64")]
use std::arch::x86_64::{__m128i, _mm_lddqu_si128, _mm_madd_epi16, _mm_maddubs_epi16, _mm_packus_epi32, _mm_storeu_si128, _mm_sub_epi8};
use std::mem::transmute;

const ZEROS: __m128i = unsafe { transmute([b'0'; 16]) };
const TEN: __m128i = unsafe { transmute([10u8, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1]) };
const HUN: __m128i = unsafe { transmute([100u8, 0, 1, 0, 100, 0, 1, 0, 100, 0, 1, 0, 100, 0, 1, 0]) };
const THO: __m128i = unsafe { transmute([16u8, 39, 1, 0, 16, 39, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) };

#[cfg(target_arch = "x86_64")]
#[target_feature(enable = "sse2")]
#[target_feature(enable = "sse3")]
#[target_feature(enable = "ssse3")]
#[target_feature(enable = "sse4.1")]
#[target_feature(enable = "sse4.2")]
// This function requests the size of 'buf' must be 16.
// If this condition is not satisfied, the behavior cannot be not defined.
pub(crate) unsafe fn parse16c(buf: &[u8]) -> u64 {
    let mut chunk = _mm_lddqu_si128(buf.as_ptr() as _);
    chunk = _mm_madd_epi16(_mm_maddubs_epi16(_mm_sub_epi8(chunk, ZEROS), TEN), HUN);
    chunk = _mm_madd_epi16(_mm_packus_epi32(chunk, chunk), THO);
    let mut buf = [0u8; 16];
    _mm_storeu_si128(buf.as_mut_ptr() as _, chunk);
    let res = u64::from_le_bytes(buf[..8].try_into().unwrap());
    ((res & 0xffffffff) * 10000_0000) + (res >> 32)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse4c_test() {
        let s = "1234".as_bytes();
        assert_eq!(unsafe { parse4c(s.try_into().unwrap()) }, 1234);

        let s = "1230".as_bytes();
        assert_eq!(unsafe { parse4lec(s.try_into().unwrap(), 3) }, 123);
    }

    #[test]
    fn parse8c_test() {
        let s = "12345678".as_bytes();
        assert_eq!(unsafe { parse8c(s.try_into().unwrap()) }, 12345678);
    }

    #[test]
    fn parse8lec_test() {
        let s = "12345678".as_bytes();
        assert_eq!(unsafe { parse8lec(s.try_into().unwrap(), 3) }, 123);
        assert_eq!(unsafe { parse8lec(s.try_into().unwrap(), 5) }, 12345);
    }

    #[test]
    fn parse16c_test() {
        let s = "1234567890123456".as_bytes();
        assert_eq!(unsafe { parse16c(s) }, 1234567890123456);
    }

    #[test]
    #[cfg(not(target_arch = "x86_64"))]
    fn parse16lec_test() {
        let s = "1234567890123456".as_bytes();
        assert_eq!(unsafe { parse16lec(s, 13) }, 1234567890123);
        assert_eq!(unsafe { parse16lec(s, 9) }, 123456789);
        assert_eq!(unsafe { parse16lec(s, 16) }, 1234567890123456);
    }
}
