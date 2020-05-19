extern crate lru;
extern crate stats_alloc;

use lru::LruCache;
use stats_alloc::{Region, StatsAlloc, INSTRUMENTED_SYSTEM};
use std::alloc::System;

#[global_allocator]
static GLOBAL: &StatsAlloc<System> = &INSTRUMENTED_SYSTEM;

#[test]
fn test_no_memory_leaks() {
  let reg = Region::new(&GLOBAL);

  {
    let mut cache = LruCache::new(2);

    cache.put("apple", "red");
    cache.put("banana", "yellow");
  }

  let stats = reg.change();
  assert_eq!(
    stats.bytes_allocated as isize,
    (stats.bytes_deallocated as isize) + stats.bytes_reallocated
  );
}
