// This function requests the size of 'buf' must be 4.
// If this condition is not satisfied, the behavior cannot be not defined.
pub(crate) unsafe fn parse4c(buf: [u8; 4]) -> u64 {
    let mut chunk = u32::from_le_bytes(buf);
    chunk -= 0x30303030;
    chunk = (chunk * 10 + (chunk >> 8)) & 0xff00ff;
    ((chunk * 100 + (chunk >> 16)) & 0xffff) as u64
}

// This function requests the size of 'buf' must be 8.
// If this condition is not satisfied, the behavior cannot be not defined.
pub(crate) unsafe fn parse8c(buf: [u8; 8]) -> u64 {
    let mut chunk = u64::from_le_bytes(buf);
    chunk -= 0x3030303030303030;
    chunk = (chunk * 10 + (chunk >> 8)) & 0xff00ff00ff00ff;
    chunk = (chunk * 100 + (chunk >> 16)) & 0xffff0000ffff;
    (chunk * 10000 + (chunk >> 32)) & 0xffffffff
}

// This function requests the size of 'buf' must be 16.
// If this condition is not satisfied, the behavior cannot be not defined.
#[cfg(not(target_arch = "x86_64"))]
pub(crate) unsafe fn parse16c(buf: &[u8]) -> u64 {
    let buf: [u8; 16] = buf.try_into().unwrap();
    let mut chunk = u128::from_le_bytes(buf);
    chunk -= 0x30303030303030303030303030303030;
    chunk = (chunk * 10 + (chunk >> 8)) & 0xff00ff00ff00ff00ff00ff00ff00ff;
    chunk = (chunk * 100 + (chunk >> 16)) & 0xffff0000ffff0000ffff0000ffff;
    chunk = (chunk * 10000 + (chunk >> 32)) & 0xffffffff00000000ffffffff;
    ((chunk * 100000000 + (chunk >> 64)) & 0xffffffffffffffff) as u64
}

#[cfg(target_arch = "x86_64")]
mod x86_64 {
    use std::arch::x86_64::{
        __m128i, _mm_cvtsi128_si64, _mm_lddqu_si128, _mm_madd_epi16, _mm_maddubs_epi16,
        _mm_packus_epi32, _mm_sub_epi8,
    };
    use std::mem::transmute;

    const ZEROS: __m128i = unsafe { transmute([b'0'; 16]) };
    const TEN: __m128i = unsafe { transmute([[10u8, 1u8]; 8]) };
    const HUN: __m128i = unsafe { transmute([[100u8, 0, 1, 0]; 4]) };
    const THO: __m128i =
        unsafe { transmute([16u8, 39, 1, 0, 16, 39, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]) };

    #[target_feature(enable = "sse2", enable = "sse3", enable = "ssse3", enable = "sse4.1")]
    // This function requests the size of 'buf' must be 16.
    // If this condition is not satisfied, the behavior cannot be not defined.
    pub unsafe fn parse16c(buf: &[u8]) -> u64 {
        let mut chunk = unsafe { _mm_lddqu_si128(buf.as_ptr() as _) };
        chunk = _mm_madd_epi16(_mm_maddubs_epi16(_mm_sub_epi8(chunk, ZEROS), TEN), HUN);
        chunk = _mm_madd_epi16(_mm_packus_epi32(chunk, chunk), THO);
        let res = _mm_cvtsi128_si64(chunk) as u64;
        ((res & 0xffffffff) * 100_000_000) + (res >> 32)
    }
}
#[cfg(target_arch = "x86_64")]
pub(crate) use x86_64::parse16c;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse4c_test() {
        let s = "1234".as_bytes();
        assert_eq!(unsafe { parse4c(s.try_into().unwrap()) }, 1234);
    }

    #[test]
    fn parse8c_test() {
        let s = "12345678".as_bytes();
        assert_eq!(unsafe { parse8c(s.try_into().unwrap()) }, 12345678);
    }

    #[test]
    fn parse16c_test() {
        let s = "1234567890123456".as_bytes();
        assert_eq!(unsafe { parse16c(s) }, 1234567890123456);
    }
}
