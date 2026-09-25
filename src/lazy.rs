use crate::{DefaultHasher, HashMap};
use alloc::borrow::Borrow;
use alloc::vec::Vec;
use core::hash::{BuildHasher, Hash};
use core::num::NonZeroUsize;
use core::sync::atomic::{AtomicU64, Ordering};

/// An LRU Cache with lazy eviction.
/// Each entry maintains an associated ordinal value representing when the
/// entry was last accessed. The cache is allowed to grow up to 2 times
/// specified capacity with no evictions, at which point, the excess entries
/// are evicted based on LRU policy resulting in an _amortized_ `O(1)`
/// performance.
pub struct LruCache<K, V, S = DefaultHasher> {
    cache: HashMap<K, (/*ordinal:*/ AtomicU64, V), S>,
    capacity: NonZeroUsize,
    counter: AtomicU64,
}

impl<K: Hash + Eq, V> LruCache<K, V> {
    /// Creates a new LRU Cache with lazy eviction.
    /// Note that the cache may contain twice as many entries as the specified
    /// capacity due to lazy eviction.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache: LruCache<isize, &str> = LruCache::new(NonZeroUsize::new(10).unwrap());
    /// ```
    pub fn new(capacity: NonZeroUsize) -> LruCache<K, V> {
        let size = capacity.get().saturating_mul(2);
        let cache = HashMap::with_capacity(size);
        Self {
            cache,
            capacity,
            counter: AtomicU64::default(),
        }
    }
}

impl<K: Hash + Eq, V, S: BuildHasher> LruCache<K, V, S> {
    /// Creates a new LRU Cache with lazy eviction and
    /// uses the provided hash builder to hash keys.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::{lazy::LruCache, DefaultHasher};
    /// use std::num::NonZeroUsize;
    ///
    /// let s = DefaultHasher::default();
    /// let mut cache: LruCache<isize, &str> = LruCache::with_hasher(NonZeroUsize::new(10).unwrap(), s);
    /// ```
    pub fn with_hasher(capacity: NonZeroUsize, hash_builder: S) -> LruCache<K, V, S> {
        let size = capacity.get().saturating_mul(2);
        let cache = HashMap::with_capacity_and_hasher(size, hash_builder);
        Self {
            cache,
            capacity,
            counter: AtomicU64::default(),
        }
    }

    /// Puts a key-value pair into cache. If the key already exists in the
    /// cache, then it updates the key's value and returns the old value.
    /// Otherwise, `None` is returned.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache = LruCache::new(NonZeroUsize::new(2).unwrap());
    ///
    /// assert_eq!(None, cache.put(1, "a"));
    /// assert_eq!(None, cache.put(2, "b"));
    /// assert_eq!(Some("b"), cache.put(2, "beta"));
    ///
    /// assert_eq!(cache.get(&1), Some(&"a"));
    /// assert_eq!(cache.get(&2), Some(&"beta"));
    /// ```
    pub fn put(&mut self, key: K, value: V) -> Option<V> {
        let ordinal = self.counter.fetch_add(1, Ordering::Relaxed);
        let old = self.cache.insert(key, (AtomicU64::new(ordinal), value));
        self.maybe_evict();
        old.map(|(_ordinal, value)| value)
    }

    // Evicts extra entries from the cache based on LRU policy if the cache has
    // grown to at least twice the self.capacity.
    fn maybe_evict(&mut self) {
        let capacity = self.capacity.get();
        let index = self.cache.len().saturating_sub(capacity);
        if index < capacity {
            return;
        }
        let mut cache: Vec<(K, (/*ordinal:*/ u64, V))> = self
            .cache
            .drain()
            .map(|(key, (ordinal, value))| (key, (ordinal.into_inner(), value)))
            .collect();
        let (_, &mut (_, (offset, _)), _) =
            cache.select_nth_unstable_by_key(index, |&(_, (ordinal, _))| ordinal);
        let mut counter = 0;
        self.cache.extend(
            cache
                .into_iter()
                .skip(index)
                .map(|(key, (ordinal, value))| {
                    let ordinal = ordinal - offset;
                    counter = counter.max(ordinal + 1);
                    (key, (AtomicU64::new(ordinal), value))
                }),
        );
        self.counter = AtomicU64::new(counter);
    }

    /// Returns a reference to the value of the key in the cache or `None` if
    /// it is not present in the cache. Updates the ordinal value associated
    /// with the entry.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache = LruCache::new(NonZeroUsize::new(2).unwrap());
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.put(3, "c");
    /// cache.put(2, "d");
    /// cache.put(4, "e");
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), Some(&"d"));
    /// assert_eq!(cache.get(&3), None);
    /// assert_eq!(cache.get(&4), Some(&"e"));
    /// ```
    pub fn get<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let (ordinal, value) = self.cache.get(key)?;
        // fetch_max instead of store here because of possible concurrent
        // lookups of the same key.
        ordinal.fetch_max(
            self.counter.fetch_add(1, Ordering::Relaxed),
            Ordering::Relaxed,
        );
        Some(value)
    }

    /// Returns a mutable reference to the value of the key in the cache or
    /// `None` if it is not present in the cache. Updates the ordinal value
    /// associated with the entry.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache = LruCache::new(NonZeroUsize::new(2).unwrap());
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("pear", 2);
    /// cache.put("banana", 6);
    /// cache.put("orange", 3);
    ///
    /// assert_eq!(cache.get_mut(&"apple"), None);
    /// assert_eq!(cache.get_mut(&"banana"), Some(&mut 6));
    /// assert_eq!(cache.get_mut(&"pear"), None);
    /// assert_eq!(cache.get_mut(&"orange"), Some(&mut 3));
    /// ```
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let (ordinal, value) = self.cache.get_mut(key)?;
        // A relaxed store is sufficient here becuase `&mut self` receiver
        // prevents concurrent mutations.
        ordinal.store(
            self.counter.fetch_add(1, Ordering::Relaxed),
            Ordering::Relaxed,
        );
        Some(value)
    }

    /// Returns a reference to the value corresponding to the key in the cache
    /// or `None` if it is not present in the cache. Unlike `get`, `peek` does
    /// not update the ordinal value associated with the entry.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache = LruCache::new(NonZeroUsize::new(2).unwrap());
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek(&1), Some(&"a"));
    /// assert_eq!(cache.peek(&2), Some(&"b"));
    /// ```
    pub fn peek<Q: ?Sized>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let (_ordinal, value) = self.cache.get(key)?;
        Some(value)
    }

    /// Returns a mutable reference to the value corresponding to the key in
    /// the cache or `None` if it is not present in the cache. Unlike
    /// `get_mut`, `peek_mut` does not update the ordinal value associated with
    /// the entry.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache = LruCache::new(NonZeroUsize::new(2).unwrap());
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek_mut(&1), Some(&mut "a"));
    /// assert_eq!(cache.peek_mut(&2), Some(&mut "b"));
    /// ```
    pub fn peek_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let (_ordinal, value) = self.cache.get_mut(key)?;
        Some(value)
    }

    /// Returns a bool indicating whether the given key is in the cache. Does
    /// not update the ordinal value associated with the entry.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache = LruCache::new(NonZeroUsize::new(2).unwrap());
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.put(3, "c");
    /// cache.put(4, "d");
    ///
    /// assert!(!cache.contains(&1));
    /// assert!(!cache.contains(&2));
    /// assert!(cache.contains(&3));
    /// assert!(cache.contains(&4));
    /// ```
    pub fn contains<Q: ?Sized>(&self, key: &Q) -> bool
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        self.cache.contains_key(key)
    }

    /// Removes and returns the value corresponding to the key from the cache
    /// or `None` if it does not exist.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache = LruCache::new(NonZeroUsize::new(2).unwrap());
    ///
    /// cache.put(2, "a");
    ///
    /// assert_eq!(cache.pop(&1), None);
    /// assert_eq!(cache.pop(&2), Some("a"));
    /// assert_eq!(cache.pop(&2), None);
    /// assert_eq!(cache.len(), 0);
    /// ```
    pub fn pop<Q: ?Sized>(&mut self, key: &Q) -> Option<V>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let (_ordinal, value) = self.cache.remove(key)?;
        Some(value)
    }

    /// Removes and returns the key and the value corresponding to the key from
    /// the cache or `None` if it does not exist.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache = LruCache::new(NonZeroUsize::new(2).unwrap());
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "a");
    ///
    /// assert_eq!(cache.pop(&1), Some("a"));
    /// assert_eq!(cache.pop_entry(&2), Some((2, "a")));
    /// assert_eq!(cache.pop(&1), None);
    /// assert_eq!(cache.pop_entry(&2), None);
    /// assert_eq!(cache.len(), 0);
    /// ```
    pub fn pop_entry<Q: ?Sized>(&mut self, key: &Q) -> Option<(K, V)>
    where
        K: Borrow<Q>,
        Q: Hash + Eq,
    {
        let (key, (_ordinal, value)) = self.cache.remove_entry(key)?;
        Some((key, value))
    }

    /// Returns the number of key-value pairs that are currently in the the
    /// cache. Note that the cache may contain twice as many entries as the
    /// specified capacity due to lazy eviction.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache = LruCache::new(NonZeroUsize::new(2).unwrap());
    /// assert_eq!(cache.len(), 0);
    ///
    /// cache.put(1, "a");
    /// assert_eq!(cache.len(), 1);
    ///
    /// cache.put(2, "b");
    /// assert_eq!(cache.len(), 2);
    ///
    /// cache.put(3, "c");
    /// assert_eq!(cache.len(), 3);
    ///
    /// cache.put(4, "d");
    /// assert_eq!(cache.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.cache.len()
    }

    /// Returns a bool indicating whether the cache is empty or not.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache = LruCache::new(NonZeroUsize::new(2).unwrap());
    /// assert!(cache.is_empty());
    ///
    /// cache.put(1, "a");
    /// assert!(!cache.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.cache.is_empty()
    }

    /// Returns the cache capacity. Note that the cache may contain twice as
    /// many entries as the specified capacity due to lazy eviction.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache: LruCache<isize, &str> = LruCache::new(NonZeroUsize::new(2).unwrap());
    /// assert_eq!(cache.cap().get(), 2);
    /// ```
    pub fn cap(&self) -> NonZeroUsize {
        self.capacity
    }

    /// Clears the contents of the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::lazy::LruCache;
    /// use std::num::NonZeroUsize;
    /// let mut cache: LruCache<isize, &str> = LruCache::new(NonZeroUsize::new(2).unwrap());
    /// assert_eq!(cache.len(), 0);
    ///
    /// cache.put(1, "a");
    /// assert_eq!(cache.len(), 1);
    ///
    /// cache.put(2, "b");
    /// assert_eq!(cache.len(), 2);
    ///
    /// cache.clear();
    /// assert_eq!(cache.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.cache.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::fmt::Debug;

    fn check_entry<K, V, S, Q: ?Sized>(cache: &LruCache<K, V, S>, key: &Q, ordinal: u64, value: V)
    where
        K: Hash + Eq + Borrow<Q>,
        Q: Hash + Eq,
        S: BuildHasher,
        V: Debug + PartialEq<V>,
    {
        let (entry_ordinal, entry_value) = cache.cache.get(key).unwrap();
        assert_eq!(entry_value, &value);
        assert_eq!(entry_ordinal.load(Ordering::Relaxed), ordinal);
    }

    #[test]
    fn test_basics() {
        let capacity = NonZeroUsize::new(2).unwrap();
        let mut cache = LruCache::new(capacity);

        cache.put("apple", 8);
        assert_eq!(cache.len(), 1);
        check_entry(&cache, "apple", 0, 8);
        assert_eq!(cache.counter.load(Ordering::Relaxed), 1);

        assert_eq!(cache.peek("apple"), Some(&8));
        check_entry(&cache, "apple", 0, 8);
        assert_eq!(cache.counter.load(Ordering::Relaxed), 1);

        assert_eq!(cache.peek_mut("apple"), Some(&mut 8));
        check_entry(&cache, "apple", 0, 8);
        assert_eq!(cache.counter.load(Ordering::Relaxed), 1);

        assert_eq!(cache.get("apple"), Some(&8));
        check_entry(&cache, "apple", 1, 8);
        assert_eq!(cache.counter.load(Ordering::Relaxed), 2);

        assert_eq!(cache.get_mut("apple"), Some(&mut 8));
        check_entry(&cache, "apple", 2, 8);
        assert_eq!(cache.counter.load(Ordering::Relaxed), 3);

        cache.put("banana", 4);
        assert_eq!(cache.len(), 2);
        check_entry(&cache, "banana", 3, 4);
        assert_eq!(cache.counter.load(Ordering::Relaxed), 4);

        cache.put("pear", 2);
        assert_eq!(cache.len(), 3);
        check_entry(&cache, "pear", 4, 2);
        assert_eq!(cache.counter.load(Ordering::Relaxed), 5);

        cache.put("banana", 6);
        assert_eq!(cache.len(), 3);
        check_entry(&cache, "banana", 5, 6);
        assert_eq!(cache.counter.load(Ordering::Relaxed), 6);

        cache.put("orange", 3); // triggers eviction
        assert_eq!(cache.len(), 2);
        check_entry(&cache, "banana", 0, 6);
        check_entry(&cache, "orange", 1, 3);
        assert_eq!(cache.counter.load(Ordering::Relaxed), 2);

        assert!(cache.contains("banana"));
        assert!(cache.contains("orange"));
        assert!(!cache.contains("apple"));
        assert!(!cache.contains("pear"));

        assert_eq!(cache.pop("banana"), Some(6));
        assert_eq!(cache.pop("banana"), None);

        assert_eq!(cache.pop_entry("orange"), Some(("orange", 3)));
        assert_eq!(cache.pop_entry("orange"), None);

        assert_eq!(cache.cap().get(), 2);
        assert_eq!(cache.len(), 0);
        assert!(cache.is_empty());
    }
}
