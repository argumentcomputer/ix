//! A reference that is either borrowed for a lifetime or shares ownership.
//!
//! Plans and backends read their program and plan through [`Shared`]. A
//! caller that keeps the program on its stack lends it for `'a`; a
//! long-lived handle shares it through an [`Arc`], so the dependent value
//! owns what it reads and needs no borrowed lifetime at all.
use std::{ops::Deref, sync::Arc};

#[derive(Debug)]
pub enum Shared<'a, T> {
  Borrowed(&'a T),
  Owned(Arc<T>),
}

impl<T> Deref for Shared<'_, T> {
  type Target = T;
  fn deref(&self) -> &T {
    match self {
      Self::Borrowed(value) => value,
      Self::Owned(value) => value,
    }
  }
}

impl<T> Clone for Shared<'_, T> {
  fn clone(&self) -> Self {
    match self {
      Self::Borrowed(value) => Self::Borrowed(value),
      Self::Owned(value) => Self::Owned(Arc::clone(value)),
    }
  }
}

impl<'a, T> From<&'a T> for Shared<'a, T> {
  fn from(value: &'a T) -> Self {
    Self::Borrowed(value)
  }
}

impl<T> From<Arc<T>> for Shared<'_, T> {
  fn from(value: Arc<T>) -> Self {
    Self::Owned(value)
  }
}
