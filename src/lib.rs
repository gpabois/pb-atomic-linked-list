use std::{marker::PhantomData, ptr::NonNull, sync::{atomic::{AtomicBool, AtomicPtr, AtomicUsize}, Arc}};

/// An atomic insert-only linked-list.
pub struct AtomicLinkedList<T>(Arc<InnerAtomicLinkedList<T>>);

impl<T> Clone for AtomicLinkedList<T> {
    fn clone(&self) -> Self {
        Self(Arc::clone(&self.0))
    }
}

impl<T> AtomicLinkedList<T> {
    /// Creates a new linked-list
    pub fn new() -> Self {
        Self(Arc::new(InnerAtomicLinkedList::new()))
    }

    /// Insert a new data within the linked list.
    /// Returns the index of the data in the list.
    pub fn insert(&self, data: T) -> usize {
        self.0.insert(data)
    }

    /// Iterate over entries references in the linked list.
    pub fn iter(&self) -> impl Iterator<Item=&T> {
        AtomicLinkIter::new(&self.0).map(|link| unsafe {&link.as_ref().data})
    }

    /// Borrow an element in the linked-list
    pub fn borrow(&self, index: usize) -> Option<&T> {
        self.iter().nth(index)
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
    raw_lock: AtomicBool,
    counter: AtomicUsize,
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
            raw_lock: AtomicBool::new(false),
            counter: AtomicUsize::new(0),
            head: AtomicPtr::default(),
            tail: AtomicPtr::default()
        }
    }
}

struct AtomicSpinlock<'a>(&'a AtomicBool);

impl<'a> AtomicSpinlock<'a> {
    pub fn acquire(atomic: &'a AtomicBool) -> Self {
        while !atomic.swap(true, std::sync::atomic::Ordering::SeqCst) {}
        Self(atomic)
    }
}

impl Drop for AtomicSpinlock<'_> {
    fn drop(&mut self) {
        self.0.swap(false, std::sync::atomic::Ordering::SeqCst);
    }
}

impl<T> InnerAtomicLinkedList<T> {
    /// Insert an element in the linked-list
    pub fn insert(&self, data: T) -> usize {
        let _lock = AtomicSpinlock::acquire(&self.raw_lock);

        let tail = self.tail.load(std::sync::atomic::Ordering::Acquire);

        let mut new_tail = NonNull::new(Box::into_raw(Box::new(
            AtomicLink::new(
                self.counter.fetch_add(1, std::sync::atomic::Ordering::Relaxed),
                data
            )
        ))).unwrap();

        unsafe {
            if tail.is_null() {
                self.head.store(new_tail.as_mut(), std::sync::atomic::Ordering::Relaxed);
                self.tail.store(new_tail.as_mut(), std::sync::atomic::Ordering::Release);
            } else {
                tail.as_mut().unwrap().next.store(new_tail.as_mut(), std::sync::atomic::Ordering::Relaxed);
                self.tail.store(new_tail.as_mut(), std::sync::atomic::Ordering::Release);
            }

            return new_tail.as_ref().index
        }
    }
}

struct AtomicLink<T> {
    index: usize,
    data: T,
    next: AtomicPtr<AtomicLink<T>>
}

impl<T> AtomicLink<T> {
    pub fn new(index: usize, data: T) -> Self {
        Self {
            index,
            data,
            next: AtomicPtr::default()
        }
    }
}

#[cfg(test)]
mod test {
    use std::{collections::HashSet, thread};

    use crate::AtomicLinkedList;

    #[test]
    fn insert_from_two_threads() {
        let ll = AtomicLinkedList::<u32>::new();

        let ll_1 = ll.clone();
        let ll_2 = ll.clone();
        
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