use std::{alloc::{dealloc, Layout}, cell::UnsafeCell, collections::HashMap, marker::PhantomData, mem::MaybeUninit, ptr::NonNull, sync::{atomic::{AtomicPtr, Ordering}, Arc}};

pub mod prelude {
    pub trait AtomicLinkedList<T> {
        /// Insert a new data within the linked list.
        /// Returns the index of the data in the list.
        fn insert(&mut self, data: T) -> usize;
        
        /// Iterate over entries references in the linked list.
        fn iter<'a>(&'a self) -> impl Iterator<Item=&T> where T: 'a;

        /// Borrow an element in the linked-list
        fn borrow<'a>(&'a self, index: usize) -> Option<&T> where T: 'a;
    }
}


/// An atomic queue based on a linked-list
pub struct AtomicQueue<T>(Arc<InnerAtomicLinkedList<T>>);

impl<T> AtomicQueue<T> {
    pub fn new() -> Self {
        Self(Arc::new(InnerAtomicLinkedList::new()))
    }

    /// Enqueue an element
    pub fn enqueue(&mut self, data: T) {
        self.0.insert(data);
    }

    /// Dequeue an element
    pub fn dequeue(&mut self) -> Option<T> {
        self.0.remove_front()
    }
}

/// An atomic insert-only linked-list.
pub struct AtomicLinkedList<T>(Arc<InnerAtomicLinkedList<T>>);

impl<T> Clone for AtomicLinkedList<T> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl<T> prelude::AtomicLinkedList<T> for AtomicLinkedList<T> {
    /// Insert a new data within the linked list.
    /// Returns the index of the data in the list.
    fn insert(&mut self, data: T) -> usize {
        self.0.insert(data)
    }

    /// Iterate over entries references in the linked list.
    fn iter<'a>(&'a self) -> impl Iterator<Item=&T> where T: 'a {
        AtomicLinkIter::new(&self.0).map(|link| unsafe {&link.as_ref().data})
    }

    /// Borrow an element in the linked-list
    fn borrow<'a>(&'a self, index: usize) -> Option<&T> where T: 'a {
        self.iter().nth(index)
    }
}

impl<T> AtomicLinkedList<T> {
    /// Creates a new linked-list
    pub fn new() -> Self {
        Self(Arc::new(InnerAtomicLinkedList::new()))
    }

    /// Get a pointer to an atomic link.
    unsafe fn get_link_ptr(&self, index: usize) -> Option<NonNull<AtomicLink<T>>> {
        AtomicLinkIter::new(&self.0).nth(index)
    }
}

/// A cached atomic linked list for faster access
pub struct CachedAtomicLinkedList<T> {
    cache: UnsafeCell<HashMap<usize, NonNull<AtomicLink<T>>>>,
    inner: AtomicLinkedList<T>
}

impl<T> CachedAtomicLinkedList<T> {
    pub fn new() -> Self {
        Self {
            cache: UnsafeCell::new(HashMap::default()),
            inner: AtomicLinkedList::new()
        }
    }
}

impl<T> From<AtomicLinkedList<T>> for CachedAtomicLinkedList<T> {
    fn from(inner: AtomicLinkedList<T>) -> Self {
       Self {
            cache: UnsafeCell::new(HashMap::default()),
            inner
       }
    }
}

impl<T> prelude::AtomicLinkedList<T> for CachedAtomicLinkedList<T> {
    /// Insert a new data within the linked list.
    /// Returns the index of the data in the list.
    fn insert(&mut self, data: T) -> usize {
        self.inner.insert(data)
    }

    /// Iterate over entries references in the linked list.
    fn iter<'a>(&'a self) -> impl Iterator<Item=&T> where T: 'a {
        self.inner.iter()
    }

    /// Borrow an element in the linked-list
    fn borrow<'a>(&'a self, index: usize) -> Option<&T> where T: 'a {
        unsafe {
            if let Some(ptr) = self.cache.get().as_mut().unwrap().get(&index) {
                Some(&ptr.as_ref().data)
            } else if let Some(ptr) =  self.inner.get_link_ptr(index) {
                self.cache.get().as_mut().unwrap().insert(index, ptr);
                Some(&ptr.as_ref().data)
            } else {
                None
            }
        }
    }
}


struct AtomicLinkIter<'a, T> {
    _phantom: std::marker::PhantomData<&'a ()>,
    ptr: *mut AtomicLink<T>
}

impl<'a, T> AtomicLinkIter<'a, T> {
    fn new(ll: &'a InnerAtomicLinkedList<T>) -> Self {
        Self {
            _phantom: PhantomData,
            ptr: ll.head.load(std::sync::atomic::Ordering::Relaxed)
        }
    }
}

impl<'a, T> Iterator for AtomicLinkIter<'a, T> {
    type Item = NonNull<AtomicLink<T>>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.ptr.is_null() {
            return None
        }

        let non_null_ptr = NonNull::new(self.ptr).unwrap();

        unsafe {
            self.ptr = non_null_ptr.as_ref().next.load(std::sync::atomic::Ordering::Relaxed);
        }

        return Some(non_null_ptr)
    }
}

/// Atomic insert-only linked list
struct InnerAtomicLinkedList<T> {
    head: AtomicPtr<AtomicLink<T>>,
    tail: AtomicPtr<AtomicLink<T>>
}

impl<T> Drop for InnerAtomicLinkedList<T> {
    fn drop(&mut self) {
        AtomicLinkIter::new(self)
        .for_each(|link| unsafe {
            link.drop_in_place();
        });
    }
}

impl<T> InnerAtomicLinkedList<T> {
    fn new() -> Self {
        Self {
            head: AtomicPtr::default(),
            tail: AtomicPtr::default()
        }
    }
}

impl<T> InnerAtomicLinkedList<T> {
    /// Insert an element in the linked-list
    pub fn insert(&self, data: T) -> usize {
        unsafe {
            let new_tail = AtomicLink::alloc_and_init(0, data).as_ptr();
            let null_ptr = std::ptr::null_mut::<AtomicLink<T>>();

            if let Ok(_) = self.tail.compare_exchange(null_ptr, new_tail, std::sync::atomic::Ordering::SeqCst, std::sync::atomic::Ordering::Relaxed) {
                self.head.store(new_tail, std::sync::atomic::Ordering::Relaxed);
                return 0;
            }

            let mut old_tail = self.tail.load(std::sync::atomic::Ordering::Relaxed);
            
            while let Err(lnk) = old_tail.as_ref().unwrap().next.compare_exchange(null_ptr, new_tail, Ordering::SeqCst, std::sync::atomic::Ordering::Relaxed) {
                old_tail = lnk;
            }
            
            new_tail.as_mut().unwrap().index = old_tail.as_ref().unwrap().index + 1;
        
            let _ = self.tail.compare_exchange(
                old_tail, 
                new_tail, 
                std::sync::atomic::Ordering::SeqCst, 
                std::sync::atomic::Ordering::Relaxed
            );

            return new_tail.as_ref().unwrap().index
        }
    }

    pub fn remove_front(&self) -> Option<T> {
        unsafe {
            let mut old_head = self.head.load(std::sync::atomic::Ordering::Relaxed);

            while let Err(next) = self.head.compare_exchange(old_head, old_head.as_ref().unwrap().next.load(std::sync::atomic::Ordering::Relaxed), std::sync::atomic::Ordering::SeqCst, std::sync::atomic::Ordering::Relaxed) {
                old_head = next;

                if old_head.is_null() {
                    return None
                }
            }
    
            let mut value = MaybeUninit::<T>::uninit().assume_init();
            let in_link_value = std::ptr::from_ref(&old_head.as_ref().unwrap().data);
            std::ptr::copy(in_link_value, std::ptr::from_mut(&mut value), 1);    
            dealloc(old_head.cast::<u8>(), Layout::new::<AtomicLink<T>>());
            
            Some(value)
        }
    }
}

struct AtomicLink<T> {
    index: usize,
    data: T,
    pub next: AtomicPtr<AtomicLink<T>>
}

impl<T> AtomicLink<T> {
    pub fn new(index: usize, data: T) -> Self {
        Self {
            index,
            data,
            next: AtomicPtr::default()
        }
    }

    unsafe fn alloc_and_init(index: usize, data: T) -> NonNull<Self> {
        let lnk = Self::new(index, data);
        NonNull::new(Box::into_raw(Box::new(lnk))).unwrap()
    }
}

#[cfg(test)]
mod test {
    use std::{collections::HashSet, thread};

    use crate::{AtomicLinkedList, AtomicQueue, prelude::AtomicLinkedList as _};

    #[test]
    fn simple_enqueue_dequeue() {
        let mut ll = AtomicQueue::<u32>::new();
        ll.enqueue(30);
        ll.enqueue(31);
        assert_eq!(ll.dequeue().unwrap(), 30);
        assert_eq!(ll.dequeue().unwrap(), 31);
    }

    #[test]
    fn insert_from_two_threads() {
        let ll = AtomicLinkedList::<u32>::new();

        let mut ll_1 = ll.clone();
        let mut ll_2 = ll.clone();
        
        let join_1 = thread::spawn(move || {
            for i in 0..=100 {
                ll_1.insert(i);
            }

        });

        let join_2 = thread::spawn(move || {
            for i in 101..=200 {
                ll_2.insert(i);
            }
        });

        join_1.join().unwrap();
        join_2.join().unwrap();

        let got = ll.iter().copied().collect::<HashSet<_>>();
        let expected = (0..=200).collect::<HashSet<_>>();

        let diff = expected.difference(&got).cloned().collect::<HashSet<_>>();
        assert_eq!(diff, HashSet::default());

    }
}