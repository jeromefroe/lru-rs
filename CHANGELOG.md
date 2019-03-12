# Changelog

## [v0.1.13](https://github.com/jeromefroe/lru-rs/tree/0.1.13) - 2018-03-12

* Bug fix to ensure that popped items are released.

## [v0.1.12](https://github.com/jeromefroe/lru-rs/tree/0.1.12) - 2018-03-04

* Replace standard HashMap with hashbrown HashMap.

## [v0.1.11](https://github.com/jeromefroe/lru-rs/tree/0.1.11) - 2018-12-10

* Implement `Iterator` trait for the cache.

## [v0.1.10](https://github.com/jeromefroe/lru-rs/tree/0.1.10) - 2018-11-07

* Add `peek_lru` method to get the least recently used element.

## [v0.1.9](https://github.com/jeromefroe/lru-rs/tree/0.1.9) - 2018-10-30

* Add `with_hasher` constructor to allow callers to use a custom hash function.

## [v0.1.8](https://github.com/jeromefroe/lru-rs/tree/0.1.8) - 2018-08-19

* Add `pop_lru` to remove least recently used element and `unbounded` constructor.

## [v0.1.7](https://github.com/jeromefroe/lru-rs/tree/0.1.7) - 2018-01-22

* Implement `Send` and `Sync` for the cache.

## [v0.1.6](https://github.com/jeromefroe/lru-rs/tree/0.1.6) - 2018-01-15

* Add `resize` method to dynamically resize the cache.

## [v0.1.5](https://github.com/jeromefroe/lru-rs/tree/0.1.5) - 2018-01-15

* Add `get_mut` method to get a mutable reference from the cache.

## [v0.1.4](https://github.com/jeromefroe/lru-rs/tree/0.1.4) - 2017-02-19

* Add function to clear the contents of the cache.

## [v0.1.3](https://github.com/jeromefroe/lru-rs/tree/0.1.3) - 2017-01-02

* Create internal hashmap with specified capacity.

## [v0.1.2](https://github.com/jeromefroe/lru-rs/tree/0.1.2) - 2017-01-02

* Add `peek` and `contains` functions.

## [v0.1.1](https://github.com/jeromefroe/lru-rs/tree/0.1.1) - 2016-12-31

* Fix documentation link in Cargo.toml.

## [v0.1.0](https://github.com/jeromefroe/lru-rs/tree/0.1.0) - 2016-12-31

* Initial release.