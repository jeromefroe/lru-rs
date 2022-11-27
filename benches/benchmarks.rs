#![feature(test)]

extern crate core;
extern crate lru;
extern crate rand;
extern crate test;

use core::num::NonZeroUsize;
use rand::Rng;
use test::Bencher;

const REPS: usize = 1 << 10;
const NUM_KEYS: usize = 1 << 20;
const CAPACITY: NonZeroUsize = unsafe { NonZeroUsize::new_unchecked(1 << 17) };

macro_rules! impl_put_bench {
    ($name: ident, $cache: ty) => {
        fn $name(bencher: &mut Bencher, capacity: NonZeroUsize, num_keys: usize, reps: usize) {
            let mut rng = rand::thread_rng();
            let mut cache = <$cache>::new(capacity);
            for _ in 0..5 * capacity.get() {
                let key = rng.gen_range(0..num_keys);
                let _ = cache.put(key, ());
            }
            bencher.iter(|| {
                for _ in 0..reps {
                    let key = rng.gen_range(0..num_keys);
                    let _ = cache.put(key, ());
                }
            });
        }
    };
}

macro_rules! impl_get_bench {
    ($name: ident, $cache: ty) => {
        fn $name(bencher: &mut Bencher, capacity: NonZeroUsize, num_keys: usize, reps: usize) {
            let mut rng = rand::thread_rng();
            let mut cache = <$cache>::new(capacity);
            for _ in 0..5 * capacity.get() {
                let key = rng.gen_range(0..num_keys);
                let _ = cache.put(key, ());
            }
            bencher.iter(|| {
                for _ in 0..reps {
                    let key = rng.gen_range(0..num_keys);
                    let _ = cache.get(&key);
                }
            });
        }
    };
}

impl_put_bench!(run_put_bench, lru::LruCache<usize, ()>);
// impl_put_bench!(run_put_bench_lazy, lru::lazy::LruCache<usize, ()>);

impl_get_bench!(run_get_bench, lru::LruCache<usize, ()>);
// impl_get_bench!(run_get_bench_lazy, lru::lazy::LruCache<usize, ()>);

#[bench]
fn bench_put(bencher: &mut Bencher) {
    run_put_bench(bencher, CAPACITY, NUM_KEYS, REPS);
}

// #[bench]
// fn bench_put_lazy(bencher: &mut Bencher) {
//     run_put_bench_lazy(bencher, CAPACITY, NUM_KEYS, REPS);
// }

#[bench]
fn bench_get(bencher: &mut Bencher) {
    run_get_bench(bencher, CAPACITY, NUM_KEYS, REPS);
}

// #[bench]
// fn bench_get_lazy(bencher: &mut Bencher) {
//     run_get_bench_lazy(bencher, CAPACITY, NUM_KEYS, REPS);
// }
