use crate::fft_cache::FftCache;
use montgomery_modint::Modulo;

pub trait NumberTheoreticTransform<M: Modulo> {
    const CACHE: FftCache<M> = FftCache::new();

    fn ntt(&mut self);
    fn intt(&mut self);
}
