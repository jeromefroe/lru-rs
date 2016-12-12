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
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.

#![feature(shared)]

use std::ptr::Shared;
use std::hash::Hash;
use std::collections::HashMap;

struct Entry<K, V> {
    prev: Option<Shared<Entry<K, V>>>,
    next: Option<Shared<Entry<K, V>>>,
    key: K,
    val: V,
}

impl<K, V> Entry<K, V> {
    fn new(key: K, val: V) -> Self {
        Entry {
            next: None,
            prev: None,
            key: key,
            val: val,
        }
    }
}

struct LinkedList<K: Eq + Clone, V> {
    head: Option<Shared<Entry<K, V>>>,
    tail: Option<Shared<Entry<K, V>>>, // might need a marker: PhantomData here
    len: usize,
    cap: usize,
}

impl<K: Eq + Clone, V> LinkedList<K, V> {
    fn new(cap: usize) -> Self {
        LinkedList {
            head: None,
            tail: None,
            len: 0,
            cap: cap,
        }
    }

    fn insert(&mut self, mut entry: Shared<Entry<K, V>>) -> Option<K> {
        let mut evicted = None;

        if self.len == self.cap {
            match self.tail {
                // we will require that self.cap > 0 so that self.tail will never be None when
                // the list is full
                None => unreachable!(),
                Some(tail) => {
                    unsafe {
                        evicted = Some((**tail).key.clone());
                    }
                    self.remove_entry(tail);
                }
            };
        }

        self.insert_head(entry);

        evicted
    }

    fn move_to_front(&mut self, mut entry: Shared<Entry<K, V>>) {
        unsafe {
            match self.head {
                None => (),
                Some(head) => {
                    if (**head).key == (**entry).key {
                        return;
                    }
                }
            }
        }

        // remove the Entry and insert it at the head
        self.remove_entry(entry);
        self.insert_head(entry);
    }

    fn insert_head(&mut self, mut entry: Shared<Entry<K, V>>) {
        unsafe {
            (**entry).next = self.head;
            (**entry).prev = None;
            let entry = Some(entry);

            match self.head {
                None => self.tail = entry,
                Some(head) => (**head).prev = entry,
            }

            self.head = entry;
            self.len += 1;
        }
    }

    fn remove_entry(&mut self, mut entry: Shared<Entry<K, V>>) {
        unsafe {
            let ref mut entry = **entry;

            match entry.prev {
                None => self.head = entry.next,
                Some(prev) => (**prev).next = entry.next,
            }

            match entry.next {
                None => self.tail = entry.prev,
                Some(next) => (**next).prev = entry.prev,
            }
        }

        self.len -= 1;
    }
}

struct LRU<K: Eq + Clone + Hash, V> {
    map: HashMap<K, Shared<Entry<K, V>>>,
    list: LinkedList<K, V>,
}

impl<K: Eq + Clone + Hash, V> LRU<K, V> {
    pub fn new(cap: usize) -> Self {
        if cap == 0 {
            panic!("LRU must have a nonzero capacity");
        }

        LRU {
            map: HashMap::with_capacity(cap),
            list: LinkedList::new(cap),
        }
    }

    pub fn get(&mut self, key: K) -> Option<&V> {
        match self.map.get(&key) {
            None => None,
            Some(val) => {
                self.list.move_to_front(*val);
                unsafe { Some(&(***val).val) }
            }
        }
    }

    pub fn put(&mut self, key: K, val: V) {
        match self.map.get(&key) {
            None => (),
            Some(entry) => {
                unsafe {
                    (***entry).val = val;
                }
                self.list.move_to_front(*entry);
                return;
            }
        }

        let entry;
        unsafe {
            entry = Shared::new(Box::into_raw(Box::new(Entry::new(key.clone(), val))));
        }
        self.map.insert(key, entry);

        let evicted = match self.list.insert(entry.clone()) {
            None => return,
            Some(evicted) => evicted,
        };

        match self.map.remove(&evicted) {
            None => unreachable!(),
            Some(val) => {
                // free the Entry by turning it back into a Box
                unsafe {
                    Box::from_raw(*val);
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::LRU;

    #[test]
    fn it_works() {
        let mut lru = LRU::new(4);

        lru.put(1, 100);

        assert_eq!(lru.get(1), Some(&100));
        assert_eq!(lru.get(2), None);

        lru.put(2, 200);
        lru.put(3, 300);

        assert_eq!(lru.get(1), Some(&100));
        assert_eq!(lru.get(2), Some(&200));
        assert_eq!(lru.get(3), Some(&300));
        assert_eq!(lru.get(4), None);

        lru.put(4, 400);
        lru.put(5, 500);

        assert_eq!(lru.get(1), None);
        assert_eq!(lru.get(2), Some(&200));
        assert_eq!(lru.get(3), Some(&300));
        assert_eq!(lru.get(4), Some(&400));
        assert_eq!(lru.get(5), Some(&500));
    }
}
