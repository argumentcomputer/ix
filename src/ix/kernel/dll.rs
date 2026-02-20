use core::marker::PhantomData;
use core::ptr::NonNull;

#[derive(Debug)]
#[allow(clippy::upper_case_acronyms)]
pub struct DLL<T> {
  pub next: Option<NonNull<DLL<T>>>,
  pub prev: Option<NonNull<DLL<T>>>,
  pub elem: T,
}

pub struct Iter<'a, T> {
  next: Option<NonNull<DLL<T>>>,
  marker: PhantomData<&'a mut DLL<T>>,
}

impl<'a, T> Iterator for Iter<'a, T> {
  type Item = &'a T;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.next.map(|node| {
      let deref = unsafe { &*node.as_ptr() };
      self.next = deref.next;
      &deref.elem
    })
  }
}

pub struct IterMut<'a, T> {
  next: Option<NonNull<DLL<T>>>,
  marker: PhantomData<&'a mut DLL<T>>,
}

impl<'a, T> Iterator for IterMut<'a, T> {
  type Item = &'a mut T;

  #[inline]
  fn next(&mut self) -> Option<Self::Item> {
    self.next.map(|node| {
      let deref = unsafe { &mut *node.as_ptr() };
      self.next = deref.next;
      &mut deref.elem
    })
  }
}

impl<T> DLL<T> {
  #[inline]
  pub fn singleton(elem: T) -> Self {
    DLL { next: None, prev: None, elem }
  }

  #[inline]
  pub fn alloc(elem: T) -> NonNull<Self> {
    NonNull::new(Box::into_raw(Box::new(Self::singleton(elem)))).unwrap()
  }

  #[inline]
  pub fn is_singleton(dll: Option<NonNull<Self>>) -> bool {
    dll.is_some_and(|dll| unsafe {
      let dll = &*dll.as_ptr();
      dll.prev.is_none() && dll.next.is_none()
    })
  }

  #[inline]
  pub fn is_empty(dll: Option<NonNull<Self>>) -> bool {
    dll.is_none()
  }

  pub fn merge(&mut self, node: NonNull<Self>) {
    unsafe {
      (*node.as_ptr()).prev = self.prev;
      (*node.as_ptr()).next = NonNull::new(self);
      if let Some(ptr) = self.prev {
        (*ptr.as_ptr()).next = Some(node);
      }
      self.prev = Some(node);
    }
  }

  pub fn unlink_node(&self) -> Option<NonNull<Self>> {
    unsafe {
      let next = self.next;
      let prev = self.prev;
      if let Some(next) = next {
        (*next.as_ptr()).prev = prev;
      }
      if let Some(prev) = prev {
        (*prev.as_ptr()).next = next;
      }
      prev.or(next)
    }
  }

  pub fn first(mut node: NonNull<Self>) -> NonNull<Self> {
    loop {
      let prev = unsafe { (*node.as_ptr()).prev };
      match prev {
        None => break,
        Some(ptr) => node = ptr,
      }
    }
    node
  }

  pub fn last(mut node: NonNull<Self>) -> NonNull<Self> {
    loop {
      let next = unsafe { (*node.as_ptr()).next };
      match next {
        None => break,
        Some(ptr) => node = ptr,
      }
    }
    node
  }

  pub fn concat(dll: NonNull<Self>, rest: Option<NonNull<Self>>) {
    let last = DLL::last(dll);
    let first = rest.map(DLL::first);
    unsafe {
      (*last.as_ptr()).next = first;
    }
    if let Some(first) = first {
      unsafe {
        (*first.as_ptr()).prev = Some(last);
      }
    }
  }

  #[inline]
  pub fn iter_option(dll: Option<NonNull<Self>>) -> Iter<'static, T> {
    Iter { next: dll.map(DLL::first), marker: PhantomData }
  }

  #[inline]
  #[allow(dead_code)]
  pub fn iter_mut_option(dll: Option<NonNull<Self>>) -> IterMut<'static, T> {
    IterMut { next: dll.map(DLL::first), marker: PhantomData }
  }

  #[allow(unsafe_op_in_unsafe_fn)]
  pub unsafe fn free_all(dll: Option<NonNull<Self>>) {
    if let Some(start) = dll {
      let first = DLL::first(start);
      let mut current = Some(first);
      while let Some(node) = current {
        let next = (*node.as_ptr()).next;
        drop(Box::from_raw(node.as_ptr()));
        current = next;
      }
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn to_vec<T: Copy + 'static>(dll: Option<NonNull<DLL<T>>>) -> Vec<T> {
    DLL::iter_option(dll).copied().collect()
  }

  #[test]
  fn test_singleton() {
    let dll = DLL::alloc(42);
    assert!(DLL::is_singleton(Some(dll)));
    unsafe {
      assert_eq!((*dll.as_ptr()).elem, 42);
      drop(Box::from_raw(dll.as_ptr()));
    }
  }

  #[test]
  fn test_is_empty() {
    assert!(DLL::<i32>::is_empty(None));
    let dll = DLL::alloc(1);
    assert!(!DLL::is_empty(Some(dll)));
    unsafe { DLL::free_all(Some(dll)) };
  }

  #[test]
  fn test_merge() {
    unsafe {
      let a = DLL::alloc(1);
      let b = DLL::alloc(2);
      (*a.as_ptr()).merge(b);
      assert_eq!(to_vec(Some(a)), vec![2, 1]);
      DLL::free_all(Some(a));
    }
  }

  #[test]
  fn test_concat() {
    unsafe {
      let a = DLL::alloc(1);
      let b = DLL::alloc(2);
      DLL::concat(a, Some(b));
      assert_eq!(to_vec(Some(a)), vec![1, 2]);
      DLL::free_all(Some(a));
    }
  }

  #[test]
  fn test_unlink_singleton() {
    unsafe {
      let dll = DLL::alloc(42);
      let remaining = (*dll.as_ptr()).unlink_node();
      assert!(remaining.is_none());
      drop(Box::from_raw(dll.as_ptr()));
    }
  }
}
