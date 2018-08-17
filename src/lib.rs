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

//! An implementation of a LRU cache. The cache supports `get`, `get_mut`, `put`,
//! and `pop` operations, all of which are O(1). This crate was heavily influenced
//! by the [LRU Cache implementation in an earlier version of Rust's std::collections crate] (https://doc.rust-lang.org/0.12.0/std/collections/lru_cache/struct.LruCache.html).
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
//!         cache.put("apple", 3);
//!         cache.put("banana", 2);
//!
//!         assert_eq!(*cache.get(&"apple").unwrap(), 3);
//!         assert_eq!(*cache.get(&"banana").unwrap(), 2);
//!         assert!(cache.get(&"pear").is_none());
//!
//!         cache.put("pear", 4);
//!
//!         assert_eq!(*cache.get(&"pear").unwrap(), 4);
//!         assert_eq!(*cache.get(&"banana").unwrap(), 2);
//!         assert!(cache.get(&"apple").is_none());
//!
//!         {
//!             let v = cache.get_mut(&"banana").unwrap();
//!             *v = 6;
//!         }
//!
//!         assert_eq!(*cache.get(&"banana").unwrap(), 6);
//! }
//! ```

#[cfg(test)]
extern crate scoped_threadpool;

use std::collections::HashMap;
use std::hash::{Hash, Hasher};
use std::mem;
use std::ptr;

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
            key,
            val,
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
    /// Creates a new LRU Cache that holds at most `cap` items.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache: LruCache<isize, &str> = LruCache::new(10);
    /// ```
    pub fn new(cap: usize) -> LruCache<K, V> {
        // NB: The compiler warns that cache does not need to be marked as mutable if we
        // declare it as such since we only mutate it inside the unsafe block.
        let cache = LruCache {
            map: HashMap::with_capacity(cap),
            cap,
            head: unsafe { Box::into_raw(Box::new(mem::uninitialized::<LruEntry<K, V>>())) },
            tail: unsafe { Box::into_raw(Box::new(mem::uninitialized::<LruEntry<K, V>>())) },
        };

        unsafe {
            (*cache.head).next = cache.tail;
            (*cache.tail).prev = cache.head;
        }

        cache
    }

    /// Puts a key-value pair into cache. If the key already exists it updates its value.
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
                    let old_key = KeyRef {
                        k: unsafe { &(*(*self.tail).prev).key },
                    };
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

    /// Returns a reference to the value of the key in the cache or `None` if it is not
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
        let key = KeyRef { k };
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

    /// Returns a mutable reference to the value of the key in the cache or `None` if it
    /// is not present in the cache. Moves the key to the head of the LRU list if it exists.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache = LruCache::new(2);
    ///
    /// cache.put("apple", 8);
    /// cache.put("banana", 4);
    /// cache.put("banana", 6);
    /// cache.put("pear", 2);
    ///
    /// assert_eq!(cache.get_mut(&"apple"), None);
    /// assert_eq!(cache.get_mut(&"banana"), Some(&mut 6));
    /// assert_eq!(cache.get_mut(&"pear"), Some(&mut 2));
    /// ```
    pub fn get_mut<'a>(&'a mut self, k: &K) -> Option<&'a mut V> {
        let key = KeyRef { k };
        let (node_ptr, value) = match self.map.get_mut(&key) {
            None => (None, None),
            Some(node) => {
                let node_ptr: *mut LruEntry<K, V> = &mut **node;
                // we need to use node_ptr to get a reference to val here because
                // detach and attach require a mutable reference to self here which
                // would be disallowed if we set value equal to &node.val
                (Some(node_ptr), Some(unsafe { &mut (*node_ptr).val }))
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

    /// Returns the value corresponding to the key in the cache or `None` if it is not
    /// present in the cache. Unlike `get`, `peek` does not update the LRU list so the
    /// key's position will be unchanged.
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
        let key = KeyRef { k };
        match self.map.get(&key) {
            None => None,
            Some(node) => Some(&node.val),
        }
    }

    /// Returns a bool indicating whether the given key is in the cache. Does not update the
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
        let key = KeyRef { k };
        self.map.contains_key(&key)
    }

    /// Removes and returns the value corresponding to the key from the cache or
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
        let key = KeyRef { k };
        match self.map.remove(&key) {
            None => None,
            Some(lru_entry) => Some(lru_entry.val),
        }
    }

    /// Returns the number of key-value pairs that are currently in the the cache.
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

    /// Returns a bool indicating whether the cache is empty or not.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache = LruCache::new(2);
    /// assert!(cache.is_empty());
    ///
    /// cache.put(1, "a");
    /// assert!(!cache.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.map.len() == 0
    }

    /// Returns the maximum number of key-value pairs the cache can hold.
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

    /// Resizes the cache. If the new capacity is smaller than the size of the current
    /// cache any entries past the new capacity are discarded.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache: LruCache<isize, &str> = LruCache::new(2);
    ///
    /// cache.put(1, "a");
    /// cache.put(2, "b");
    /// cache.resize(4);
    /// cache.put(3, "c");
    /// cache.put(4, "d");
    ///
    /// assert_eq!(cache.len(), 4);
    /// assert_eq!(cache.get(&1), Some(&"a"));
    /// assert_eq!(cache.get(&2), Some(&"b"));
    /// assert_eq!(cache.get(&3), Some(&"c"));
    /// assert_eq!(cache.get(&4), Some(&"d"));
    /// ```
    pub fn resize(&mut self, cap: usize) {
        // return early if capacity doesn't change
        if cap == self.cap {
            return;
        }

        let mut new_map: HashMap<KeyRef<K>, Box<LruEntry<K, V>>> = HashMap::with_capacity(cap);

        let mut current;
        unsafe { current = (*self.head).next };
        while current != self.tail {
            if new_map.len() < cap {
                let key = unsafe { &(*current).key };
                let keyref = KeyRef { k: key };

                // remove node from old map so its destructor isn't run
                let node = self.map.remove(&keyref).unwrap();
                new_map.insert(keyref, node);

                unsafe { current = (*current).next }
            } else {
                // we are at max capacity so we can just update the tail and break
                self.detach(current);
                unsafe {
                    (*(*current).prev).next = self.tail;
                    self.tail = (*current).prev;
                }
                break;
            }
        }

        self.map = new_map;
        self.cap = cap;
    }

    /// Clears the contents of the cache.
    ///
    /// # Example
    ///
    /// ```
    /// use lru::LruCache;
    /// let mut cache: LruCache<isize, &str> = LruCache::new(2);
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
        loop {
            let prev;
            unsafe { prev = (*self.tail).prev }
            if prev != self.head {
                let old_key = KeyRef {
                    k: unsafe { &(*(*self.tail).prev).key },
                };
                let mut old_node = self.map.remove(&old_key).unwrap();
                let node_ptr: *mut LruEntry<K, V> = &mut *old_node;
                self.detach(node_ptr);
            } else {
                break;
            }
        }
    }

    fn detach(&mut self, node: *mut LruEntry<K, V>) {
        unsafe {
            (*(*node).prev).next = (*node).next;
            (*(*node).next).prev = (*node).prev;
        }
    }

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
            let head = *Box::from_raw(self.head);
            let tail = *Box::from_raw(self.tail);

            let LruEntry {
                key: head_key,
                val: head_val,
                ..
            } = head;
            let LruEntry {
                key: tail_key,
                val: tail_val,
                ..
            } = tail;

            mem::forget(head_key);
            mem::forget(head_val);
            mem::forget(tail_key);
            mem::forget(tail_val);
        }
    }
}

// The compiler does not automatically derive Send and Sync for LruCache because it contains
// raw pointers. The raw pointers are safely encapsulated by LruCache though so we can
// implement Send and Sync for it below.
unsafe impl<K: Sync + Send, V: Sync + Send> Send for LruCache<K, V> {}
unsafe impl<K: Sync + Send, V: Sync + Send> Sync for LruCache<K, V> {}

#[cfg(test)]
mod tests {
    use super::LruCache;
    use scoped_threadpool::Pool;
    use std::fmt::Debug;

    fn assert_opt_eq<V: PartialEq + Debug>(opt: Option<&V>, v: V) {
        assert!(opt.is_some());
        assert_eq!(opt.unwrap(), &v);
    }

    fn assert_opt_eq_mut<V: PartialEq + Debug>(opt: Option<&mut V>, v: V) {
        assert!(opt.is_some());
        assert_eq!(opt.unwrap(), &v);
    }

    #[test]
    fn test_put_and_get() {
        let mut cache = LruCache::new(2);
        assert!(cache.is_empty());

        cache.put("apple", "red");
        cache.put("banana", "yellow");

        assert_eq!(cache.cap(), 2);
        assert_eq!(cache.len(), 2);
        assert!(!cache.is_empty());
        assert_opt_eq(cache.get(&"apple"), "red");
        assert_opt_eq(cache.get(&"banana"), "yellow");
    }

    #[test]
    fn test_put_and_get_mut() {
        let mut cache = LruCache::new(2);

        cache.put("apple", "red");
        cache.put("banana", "yellow");

        assert_eq!(cache.cap(), 2);
        assert_eq!(cache.len(), 2);
        assert_opt_eq_mut(cache.get_mut(&"apple"), "red");
        assert_opt_eq_mut(cache.get_mut(&"banana"), "yellow");
    }

    #[test]
    fn test_get_mut_and_update() {
        let mut cache = LruCache::new(2);

        cache.put("apple", 1);
        cache.put("banana", 3);

        {
            let v = cache.get_mut(&"apple").unwrap();
            *v = 4;
        }

        assert_eq!(cache.cap(), 2);
        assert_eq!(cache.len(), 2);
        assert_opt_eq_mut(cache.get_mut(&"apple"), 4);
        assert_opt_eq_mut(cache.get_mut(&"banana"), 3);
    }

    #[test]
    fn test_put_update() {
        let mut cache = LruCache::new(1);

        cache.put("apple", "red");
        cache.put("apple", "green");

        assert_eq!(cache.len(), 1);
        assert_opt_eq(cache.get(&"apple"), "green");
    }

    #[test]
    fn test_put_removes_oldest() {
        let mut cache = LruCache::new(2);

        cache.put("apple", "red");
        cache.put("banana", "yellow");
        cache.put("pear", "green");

        assert!(cache.get(&"apple").is_none());
        assert_opt_eq(cache.get(&"banana"), "yellow");
        assert_opt_eq(cache.get(&"pear"), "green");

        cache.put("banana", "green");
        cache.put("tomato", "red");

        assert!(cache.get(&"pear").is_none());
        assert_opt_eq(cache.get(&"banana"), "green");
        assert_opt_eq(cache.get(&"tomato"), "red");
    }

    #[test]
    fn test_peek() {
        let mut cache = LruCache::new(2);

        cache.put("apple", "red");
        cache.put("banana", "yellow");

        assert_opt_eq(cache.peek(&"banana"), "yellow");
        assert_opt_eq(cache.peek(&"apple"), "red");

        cache.put("pear", "green");

        assert!(cache.peek(&"apple").is_none());
        assert_opt_eq(cache.peek(&"banana"), "yellow");
        assert_opt_eq(cache.peek(&"pear"), "green");
    }

    #[test]
    fn test_contains() {
        let mut cache = LruCache::new(2);

        cache.put("apple", "red");
        cache.put("banana", "yellow");
        cache.put("pear", "green");

        assert!(!cache.contains(&"apple"));
        assert!(cache.contains(&"banana"));
        assert!(cache.contains(&"pear"));
    }

    #[test]
    fn test_pop() {
        let mut cache = LruCache::new(2);

        cache.put("apple", "red");
        cache.put("banana", "yellow");

        assert_eq!(cache.len(), 2);
        assert_opt_eq(cache.get(&"apple"), "red");
        assert_opt_eq(cache.get(&"banana"), "yellow");

        let popped = cache.pop(&"apple");
        assert!(popped.is_some());
        assert_eq!(popped.unwrap(), "red");
        assert_eq!(cache.len(), 1);
        assert!(cache.get(&"apple").is_none());
        assert_opt_eq(cache.get(&"banana"), "yellow");
    }

    #[test]
    fn test_clear() {
        let mut cache = LruCache::new(2);

        cache.put("apple", "red");
        cache.put("banana", "yellow");

        assert_eq!(cache.len(), 2);
        assert_opt_eq(cache.get(&"apple"), "red");
        assert_opt_eq(cache.get(&"banana"), "yellow");

        cache.clear();
        assert_eq!(cache.len(), 0);
    }

    #[test]
    fn test_resize_larger() {
        let mut cache = LruCache::new(2);

        cache.put(1, "a");
        cache.put(2, "b");
        cache.resize(4);
        cache.put(3, "c");
        cache.put(4, "d");

        assert_eq!(cache.len(), 4);
        assert_eq!(cache.get(&1), Some(&"a"));
        assert_eq!(cache.get(&2), Some(&"b"));
        assert_eq!(cache.get(&3), Some(&"c"));
        assert_eq!(cache.get(&4), Some(&"d"));
    }

    #[test]
    fn test_resize_smaller() {
        let mut cache = LruCache::new(4);

        cache.put(1, "a");
        cache.put(2, "b");
        cache.put(3, "c");
        cache.put(4, "d");

        cache.resize(2);

        assert_eq!(cache.len(), 2);
        assert!(cache.get(&1).is_none());
        assert!(cache.get(&2).is_none());
        assert_eq!(cache.get(&3), Some(&"c"));
        assert_eq!(cache.get(&4), Some(&"d"));
    }

    #[test]
    fn test_send() {
        use std::thread;

        let mut cache = LruCache::new(4);
        cache.put(1, "a");

        let handle = thread::spawn(move || {
            assert_eq!(cache.get(&1), Some(&"a"));
        });

        assert!(handle.join().is_ok());
    }

    #[test]
    fn test_sync() {
        let mut pool = Pool::new(1);
        let mut cache = LruCache::new(4);
        cache.put(1, "a");

        let cache_ref = &cache;
        pool.scoped(|scoped| {
            scoped.execute(move || {
                assert_eq!(cache_ref.peek(&1), Some(&"a"));
            });
        });

        assert_eq!((cache_ref).peek(&1), Some(&"a"));
    }
}
