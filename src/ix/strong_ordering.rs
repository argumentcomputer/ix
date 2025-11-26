use std::cmp::Ordering;

#[derive(Clone)]
pub struct SOrd {
  pub strong: bool,
  pub ordering: Ordering,
}

impl SOrd {
  pub fn eq(strong: bool) -> Self {
    SOrd { strong, ordering: Ordering::Equal }
  }
  pub fn lt(strong: bool) -> Self {
    SOrd { strong, ordering: Ordering::Less }
  }
  pub fn gt(strong: bool) -> Self {
    SOrd { strong, ordering: Ordering::Greater }
  }

  pub fn compare(self, other: Self) -> Self {
    match self {
      SOrd { strong: true, ordering: Ordering::Equal } => other,
      SOrd { strong: false, ordering: Ordering::Equal } => {
        SOrd { strong: false, ordering: other.ordering }
      },
      _ => self,
    }
  }

  pub fn cmp<A: Ord>(x: &A, y: &A) -> Self {
    SOrd { strong: true, ordering: x.cmp(y) }
  }

  #[inline]
  pub fn try_compare<E, F>(self, other: F) -> Result<Self, E>
  where
    F: FnOnce() -> Result<Self, E>,
  {
    match self {
      SOrd { strong: true, ordering: Ordering::Equal } => other(),
      SOrd { strong: false, ordering: Ordering::Equal } => {
        other().map(|s| SOrd { strong: false, ordering: s.ordering })
      },
      _ => Ok(self),
    }
  }

  #[inline]
  pub fn try_zip<T, E, F>(mut f: F, xs: &[T], ys: &[T]) -> Result<Self, E>
  where
    F: FnMut(&T, &T) -> Result<Self, E>,
  {
    match (xs, ys) {
      ([], []) => Ok(SOrd::eq(true)),
      ([], _) => Ok(SOrd::lt(true)),
      (_, []) => Ok(SOrd::gt(true)),
      ([x, xs_rest @ ..], [y, ys_rest @ ..]) => {
        let result = f(x, y)?;
        match result {
          SOrd { strong: true, ordering: Ordering::Equal } => {
            Self::try_zip(f, xs_rest, ys_rest)
          },
          SOrd { strong: false, ordering: Ordering::Equal } => {
            Self::try_zip(f, xs_rest, ys_rest)
              .map(|s| SOrd { strong: false, ordering: s.ordering })
          },
          _ => Ok(result),
        }
      },
    }
  }
}
