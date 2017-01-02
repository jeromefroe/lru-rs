// MIT License

// Copyright (c) 2016 Jerome Froelich

// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:

// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.

// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNpubESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

//! An implementation of a LRU cache. The cache supports `get`, `put`, and `remove`
//! operations, all of which are O(1). This crate was heavily influenced by the
//! [LRU Cache implementation in an earlier version of Rust's std::collections crate] (https://doc.rust-lang.org/0.12.0/std/collections/lru_cache/struct.LruCache.html).
//!
//! ## Example
//!
//! ```rust,no_run
//! extern crate lru;
//!
//! use lru::LruCache;
//!
//! fn main() {
//!         let mut cache = LruCache::new(2);
//!         cache.put("apple".to_string(), "red".to_string());
//!         cache.put("banana".to_string(), "yellow".to_string());
//!
//!         assert_eq!(*cache.get(&"apple".to_string()).unwrap(), "red".to_string());
//!         assert_eq!(*cache.get(&"banana".to_string()).unwrap(), "yellow".to_string());
//!         assert!(cache.get(&"pear".to_string()).is_none());
//!
//!         cache.put("pear".to_string(), "green".to_string());
//!
//!         assert_eq!(*cache.get(&"pear".to_string()).unwrap(), "green".to_string());
//!         assert_eq!(*cache.get(&"banana".to_string()).unwrap(), "yellow".to_string());
//!         assert!(cache.get(&"apple".to_string()).is_none());
//! }
//! ```

#![feature(box_patterns)]

use std::mem;
use std::ptr;
use std::hash::{Hash, Hasher};
use std::collections::HashMap;

// Struct used to hold a reference to a key
struct KeyRef<K> {
    k: *const K,
}

impl<K: Hash> Hash for KeyRef<K> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        unsafe { (*self.k).hash(state) }
    }
}

impl<K: PartialEq> PartialEq for KeyRef<K> {
    fn eq(&self, other: &KeyRef<K>) -> bool {
        unsafe { (*self.k).eq(&*other.k) }
    }
}

impl<K: Eq> Eq for KeyRef<K> {}

// Struct used to hold a key value pair. Also contains references to previous and next entries
// so we can maintain the entries in a linked list ordered by their use.
struct LruEntry<K, V> {
    key: K,
    val: V,
    prev: *mut LruEntry<K, V>,
    next: *mut LruEntry<K, V>,
}

impl<K, V> LruEntry<K, V> {
    fn new(key: K, val: V) -> Self {
        LruEntry {
            key: key,
            val: val,
            prev: ptr::null_mut(),
            next: ptr::null_mut(),
        }
    }
}

/// An LRU Cache
pub struct LruCache<K, V> {
    map: HashMap<KeyRef<K>, Box<LruEntry<K, V>>>,
    cap: usize,

    // head and tail are sigil nodes to faciliate inserting entries
    head: *mut LruEntry<K, V>,
    tail: *mut LruEntry<K, V>,
}

impl<K: Hash + Eq, V> LruCache<K, V> {
    /// Create a new LRU Cache that holds at most `cap` items.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache: LruCache<isize, &str> = LruCache::new(10);
    /// ```
    pub fn new(cap: usize) -> LruCache<K, V> {
        let mut cache = LruCache {
            map: HashMap::new(),
            cap: cap,
            head: unsafe { Box::into_raw(Box::new(mem::uninitialized::<LruEntry<K, V>>())) },
            tail: unsafe { Box::into_raw(Box::new(mem::uninitialized::<LruEntry<K, V>>())) },
        };

        unsafe {
            (*cache.head).next = cache.tail;
            (*cache.tail).prev = cache.head;
        }

        cache
    }

    /// Put a key-value pair into cache. If the key already exists update its value.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// assert_eq!(cache.get(&1), Some(&"a"));
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// ```
    pub fn put(&mut self, k: K, v: V) {
        let node_ptr = self.map.get_mut(&KeyRef { k: &k }).map(|node| {
            let node_ptr: *mut LruEntry<K, V> = &mut **node;
            node_ptr
        });

        match node_ptr {
            Some(node_ptr) => {
                // if the key is already in the cache just update its value and move it to the
                // front of the list
                unsafe { (*node_ptr).val = v };
                self.detach(node_ptr);
                self.attach(node_ptr);
            }
            None => {
                let mut node = if self.len() == self.cap() {
                    // if the cache is full, remove the last entry so we can use it for the new key
                    let old_key = KeyRef { k: unsafe { &(*(*self.tail).prev).key } };
                    let mut old_node = self.map.remove(&old_key).unwrap();

                    old_node.key = k;
                    old_node.val = v;

                    let node_ptr: *mut LruEntry<K, V> = &mut *old_node;
                    self.detach(node_ptr);

                    old_node
                } else {
                    // if the cache is not full allocate a new LruEntry
                    Box::new(LruEntry::new(k, v))
                };

                let node_ptr: *mut LruEntry<K, V> = &mut *node;
                self.attach(node_ptr);

                let keyref = unsafe { &(*node_ptr).key };
                self.map.insert(KeyRef { k: keyref }, node);
            }
        }
    }

    /// Return the value corresponding to the key in the cache or `None` if it is not
    /// present in the cache. Moves the key to the head of the LRU list if it exists.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.put(2, "c");
    /// cache.put(3, "d");
    ///
    /// assert_eq!(cache.get(&1), None);
    /// assert_eq!(cache.get(&2), Some(&"c"));
    /// assert_eq!(cache.get(&3), Some(&"d"));
    /// ```
    pub fn get<'a>(&'a mut self, k: &K) -> Option<&'a V> {
        let key = KeyRef { k: k };
        let (node_ptr, value) = match self.map.get_mut(&key) {
            None => (None, None),
            Some(node) => {
                let node_ptr: *mut LruEntry<K, V> = &mut **node;
                // we need to use node_ptr to get a reference to val here because
                // detach and attach require a mutable reference to self here which
                // would be disallowed if we set value equal to &node.val
                (Some(node_ptr), Some(unsafe { &(*node_ptr).val }))
            }
        };

        match node_ptr {
            None => (),
            Some(node_ptr) => {
                self.detach(node_ptr);
                self.attach(node_ptr);
            }
        }

        value
    }

    /// Return the value corresponding to the key in the cache or `None` if it is not
    /// present in the cache. Unlike `get`, `peek` does not update the LRU list so key's
    /// position will be unchanged.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    ///
    /// assert_eq!(cache.peek(&1), Some(&"a"));
    /// assert_eq!(cache.peek(&2), Some(&"b"));
    /// ```
    pub fn peek<'a>(&'a self, k: &K) -> Option<&'a V> {
        let key = KeyRef { k: k };
        match self.map.get(&key) {
            None => None,
            Some(node) => Some(&node.val),
        }
    }

    /// Return a bool indicating whether the given key is in the cache. Does not update the
    /// LRU list.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.put(3, "c");
    ///
    /// assert!(!cache.contains(&1));
    /// assert!(cache.contains(&2));
    /// assert!(cache.contains(&3));
    /// ```
    pub fn contains(&self, k: &K) -> bool {
        let key = KeyRef { k: k };
        self.map.contains_key(&key)
    }

    /// Remove and return the value corresponding to the key from the cache or
    /// `None` if it does not exist.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.put(2, "a");
    ///
    /// assert_eq!(cache.pop(&1), None);
    /// assert_eq!(cache.pop(&2), Some("a"));
    /// assert_eq!(cache.pop(&2), None);
    /// assert_eq!(cache.len(), 0);
    /// ```
    pub fn pop(&mut self, k: &K) -> Option<V> {
        let key = KeyRef { k: k };
        match self.map.remove(&key) {
            None => None,
            Some(lru_entry) => Some(lru_entry.val),
        }
    }

    /// Return the number of key-value pairs that are currently in the the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache = LruCache::new(2);
    /// assert_eq!(cache.len(), 0);
    ///
    /// cache.put(1, "a");
    /// assert_eq!(cache.len(), 1);
    ///
    /// cache.put(2, "b");
    /// assert_eq!(cache.len(), 2);
    ///
    /// cache.put(3, "c");
    /// assert_eq!(cache.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.map.len()
    }

    /// Return the maximum number of key-value pairs the cache can hold.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache: LruCache<isize, &str> = LruCache::new(2);
    /// assert_eq!(cache.cap(), 2);
    /// ```
    pub fn cap(&self) -> usize {
        self.cap
    }

    fn detach(&mut self, node: *mut LruEntry<K, V>) {
        unsafe {
            (*(*node).prev).next = (*node).next;
            (*(*node).next).prev = (*node).prev;
        }
    }

    #[inline]
    fn attach(&mut self, node: *mut LruEntry<K, V>) {
        unsafe {
            (*node).next = (*self.head).next;
            (*node).prev = self.head;
            (*self.head).next = node;
            (*(*node).next).prev = node;
        }
    }
}

impl<K, V> Drop for LruCache<K, V> {
    fn drop(&mut self) {
        // Prevent compiler from trying to drop the un-initialized fields key and val in head
        // and tail
        unsafe {
            let head = Box::from_raw(self.head);
            let tail = Box::from_raw(self.tail);

            // presently the only way to destructure a box is with the experimental box
            // pattern syntax
            let box internal_head = head;
            let box internal_tail = tail;

            let LruEntry { next: _, prev: _, key: head_key, val: head_val } = internal_head;
            let LruEntry { next: _, prev: _, key: tail_key, val: tail_val } = internal_tail;

            mem::forget(head_key);
            mem::forget(head_val);
            mem::forget(tail_key);
            mem::forget(tail_val);
        }
    }
}

#[cfg(test)]
mod tests {
    use std::fmt::Debug;
    use super::LruCache;

    fn assert_opt_eq<V: PartialEq + Debug>(opt: Option<&V>, v: V) {
        assert!(opt.is_some());
        assert_eq!(opt.unwrap(), &v);
    }

    #[test]
    fn test_put_and_get() {
        let mut cache: LruCache<String, String> = LruCache::new(2);

        cache.put("apple".to_string(), "red".to_string());
        cache.put("banana".to_string(), "yellow".to_string());

        assert_eq!(cache.cap(), 2);
        assert_eq!(cache.len(), 2);
        assert_opt_eq(cache.get(&"apple".to_string()), "red".to_string());
        assert_opt_eq(cache.get(&"banana".to_string()), "yellow".to_string());
    }

    #[test]
    fn test_put_update() {
        let mut cache = LruCache::new(1);

        cache.put("apple".to_string(), "red".to_string());
        cache.put("apple".to_string(), "green".to_string());

        assert_eq!(cache.len(), 1);
        assert_opt_eq(cache.get(&"apple".to_string()), "green".to_string());
    }

    #[test]
    fn test_put_removes_oldest() {
        let mut cache = LruCache::new(2);

        cache.put("apple".to_string(), "red".to_string());
        cache.put("banana".to_string(), "yellow".to_string());
        cache.put("pear".to_string(), "green".to_string());

        assert!(cache.get(&"apple".to_string()).is_none());
        assert_opt_eq(cache.get(&"banana".to_string()), "yellow".to_string());
        assert_opt_eq(cache.get(&"pear".to_string()), "green".to_string());

        cache.put("banana".to_string(), "green".to_string());
        cache.put("tomato".to_string(), "red".to_string());

        assert!(cache.get(&"pear".to_string()).is_none());
        assert_opt_eq(cache.get(&"banana".to_string()), "green".to_string());
        assert_opt_eq(cache.get(&"tomato".to_string()), "red".to_string());
    }

    #[test]
    fn test_peek() {
        let mut cache: LruCache<String, String> = LruCache::new(2);

        cache.put("apple".to_string(), "red".to_string());
        cache.put("banana".to_string(), "yellow".to_string());

        assert_opt_eq(cache.peek(&"banana".to_string()), "yellow".to_string());
        assert_opt_eq(cache.peek(&"apple".to_string()), "red".to_string());

        cache.put("pear".to_string(), "green".to_string());

        assert!(cache.peek(&"apple".to_string()).is_none());
        assert_opt_eq(cache.peek(&"banana".to_string()), "yellow".to_string());
        assert_opt_eq(cache.peek(&"pear".to_string()), "green".to_string());
    }

    #[test]
    fn test_contains() {
        let mut cache = LruCache::new(2);

        cache.put("apple".to_string(), "red".to_string());
        cache.put("banana".to_string(), "yellow".to_string());
        cache.put("pear".to_string(), "green".to_string());

        assert!(!cache.contains(&"apple".to_string()));
        assert!(cache.contains(&"banana".to_string()));
        assert!(cache.contains(&"pear".to_string()));
    }

    #[test]
    fn test_pop() {
        let mut cache = LruCache::new(2);

        cache.put("apple".to_string(), "red".to_string());
        cache.put("banana".to_string(), "yellow".to_string());

        assert_eq!(cache.len(), 2);
        assert_opt_eq(cache.get(&"apple".to_string()), "red".to_string());
        assert_opt_eq(cache.get(&"banana".to_string()), "yellow".to_string());

        let popped = cache.pop(&"apple".to_string());
        assert!(popped.is_some());
        assert_eq!(popped.unwrap(), "red".to_string());
        assert_eq!(cache.len(), 1);
        assert!(cache.get(&"apple".to_string()).is_none());
        assert_opt_eq(cache.get(&"banana".to_string()), "yellow".to_string());
    }
}
