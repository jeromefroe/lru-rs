# LRU Cache

[![Build Status](https://travis-ci.org/jeromefroe/lru-rs.svg?branch=master)](https://travis-ci.org/jeromefroe/lru-rs)
[![codecov](https://codecov.io/gh/jeromefroe/lru-rs/branch/master/graph/badge.svg)](https://codecov.io/gh/jeromefroe/lru-rs)
[![crates.io](https://img.shields.io/crates/v/lru.svg)](https://crates.io/crates/lru/)
[![docs.rs](https://docs.rs/lru/badge.svg)](https://docs.rs/lru/)
[![License](https://img.shields.io/badge/license-MIT-blue.svg)](https://raw.githubusercontent.com/jeromefroe/lru-rs/master/LICENSE)

[Documentation](https://docs.rs/lru/)

An implementation of a LRU cache. The cache supports `put`, `get`, `get_mut` and `pop` operations,
all of which are O(1). This crate was heavily influenced by the
[LRU Cache implementation in an earlier version of Rust's std::collections crate](https://doc.rust-lang.org/0.12.0/std/collections/lru_cache/struct.LruCache.html).


## Example

Below is a simple example of how to instantiate and use a LRU cache.

```rust,no_run
extern crate lru;

use lru::LruCache;

fn main() {
        let mut cache = LruCache::new(2);
        cache.put("apple", 3);
        cache.put("banana", 2);

        assert_eq!(*cache.get(&"apple").unwrap(), 3);
        assert_eq!(*cache.get(&"banana").unwrap(), 2);
        assert!(cache.get(&"pear").is_none());

        cache.put("pear", 4);

        assert_eq!(*cache.get(&"pear").unwrap(), 4);
        assert_eq!(*cache.get(&"banana").unwrap(), 2);
        assert!(cache.get(&"apple").is_none());

        {
            let v = cache.get_mut(&"banana").unwrap();
            *v = 6;
        }

        assert_eq!(*cache.get(&"banana").unwrap(), 6);
}
```