# Changelog

## [v0.4.3](https://github.com/jeromefroe/lru-rs/tree/0.4.3) - 2019-12-10

- Add back import of alloc crate on nightly which was accidentally removed.

## [v0.4.2](https://github.com/jeromefroe/lru-rs/tree/0.4.2) - 2019-12-08

- Make hasbrown usage optional and add MSRV documentation.

## [v0.4.1](https://github.com/jeromefroe/lru-rs/tree/0.4.1) - 2019-11-26

- Use `mem::MaybeUninit` instead of `mem::uninitialized`.

## [v0.4.0](https://github.com/jeromefroe/lru-rs/tree/0.4.0) - 2019-10-28

- Use `Borrow` trait in `contains` and `pop` methods.

## [v0.3.1](https://github.com/jeromefroe/lru-rs/tree/0.3.1) - 2019-10-08

- Implement `Debug` for `LruCache`.

## [v0.3.0](https://github.com/jeromefroe/lru-rs/tree/0.3.0) - 2019-10-06

- Update the signature of the `peek` methods to use the `Borrow` trait and add a `peek_mut` method.

## [v0.2.0](https://github.com/jeromefroe/lru-rs/tree/0.2.0) - 2019-09-27

- Release a new minor version because of an accidental breaking change in the previous release ([#50](https://github.com/jeromefroe/lru-rs/issues/50)).

## [v0.1.18](https://github.com/jeromefroe/lru-rs/tree/0.1.18) - 2019-09-25

- Add borrowed type support for get_mut.

## [v0.1.17](https://github.com/jeromefroe/lru-rs/tree/0.1.17) - 2019-08-21

- Return Option from put method which contains old value if it exists.

## [v0.1.16](https://github.com/jeromefroe/lru-rs/tree/0.1.16) - 2019-07-25

- Implement Borrow trait for KeyRef with nightly OIBIT feature.

## [v0.1.15](https://github.com/jeromefroe/lru-rs/tree/0.1.15) - 2019-04-13

- Make crate no_std compatible with nightly feature.

## [v0.1.14](https://github.com/jeromefroe/lru-rs/tree/0.1.14) - 2019-04-13

- Implement `IterMut` to be able to get a mutable iterator for the cache.

## [v0.1.13](https://github.com/jeromefroe/lru-rs/tree/0.1.13) - 2019-03-12

- Bug fix to ensure that popped items are released.

## [v0.1.12](https://github.com/jeromefroe/lru-rs/tree/0.1.12) - 2019-03-04

- Replace standard HashMap with hashbrown HashMap.

## [v0.1.11](https://github.com/jeromefroe/lru-rs/tree/0.1.11) - 2018-12-10

- Implement `Iterator` trait for the cache.

## [v0.1.10](https://github.com/jeromefroe/lru-rs/tree/0.1.10) - 2018-11-07

- Add `peek_lru` method to get the least recently used element.

## [v0.1.9](https://github.com/jeromefroe/lru-rs/tree/0.1.9) - 2018-10-30

- Add `with_hasher` constructor to allow callers to use a custom hash function.

## [v0.1.8](https://github.com/jeromefroe/lru-rs/tree/0.1.8) - 2018-08-19

- Add `pop_lru` to remove least recently used element and `unbounded` constructor.

## [v0.1.7](https://github.com/jeromefroe/lru-rs/tree/0.1.7) - 2018-01-22

- Implement `Send` and `Sync` for the cache.

## [v0.1.6](https://github.com/jeromefroe/lru-rs/tree/0.1.6) - 2018-01-15

- Add `resize` method to dynamically resize the cache.

## [v0.1.5](https://github.com/jeromefroe/lru-rs/tree/0.1.5) - 2018-01-15

- Add `get_mut` method to get a mutable reference from the cache.

## [v0.1.4](https://github.com/jeromefroe/lru-rs/tree/0.1.4) - 2017-02-19

- Add function to clear the contents of the cache.

## [v0.1.3](https://github.com/jeromefroe/lru-rs/tree/0.1.3) - 2017-01-02

- Create internal hashmap with specified capacity.

## [v0.1.2](https://github.com/jeromefroe/lru-rs/tree/0.1.2) - 2017-01-02

- Add `peek` and `contains` functions.

## [v0.1.1](https://github.com/jeromefroe/lru-rs/tree/0.1.1) - 2016-12-31

- Fix documentation link in Cargo.toml.

## [v0.1.0](https://github.com/jeromefroe/lru-rs/tree/0.1.0) - 2016-12-31

- Initial release.
