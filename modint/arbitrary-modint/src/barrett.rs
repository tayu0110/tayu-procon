// https://natsugiri.hatenablog.com/entry/2020/04/06/030559
#[derive(Debug, Clone, Copy)]
pub(crate) struct BarrettReduction {
    modulo: u32,
    m: u128,
}

impl BarrettReduction {
    pub const fn new(modulo: u32) -> Self {
        let m = (1u128 << 64) / modulo as u128;
        Self { modulo, m }
    }

    pub const fn reduce(self, mut x: u64) -> u32 {
        if x < self.modulo as u64 {
            return x as u32;
        }
        let q = ((self.m * x as u128) >> 64) as u64;
        x -= q * self.modulo as u64;
        (x - (x >= self.modulo as u64) as u64 * self.modulo as u64) as u32
    }

    pub const fn modulo(self) -> u32 {
        self.modulo
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn barret_reduction_test() {
        const BARRETT: BarrettReduction = BarrettReduction::new(998244353);
        assert_eq!(BARRETT.reduce(0), 0);
        assert_eq!(BARRETT.reduce(1000000000), 1000000000 % 998244353);
        assert_eq!(BARRETT.reduce(549435274), 549435274);
    }
}
