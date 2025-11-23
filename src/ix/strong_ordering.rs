use std::cmp::Ordering;

#[derive(Clone)]
pub struct SOrder {
  pub strong: bool,
  pub ordering: Ordering,
}

impl SOrder {
  pub fn eq(strong: bool) -> Self {
    SOrder { strong, ordering: Ordering::Equal }
  }
  pub fn lt(strong: bool) -> Self {
    SOrder { strong, ordering: Ordering::Less }
  }
  pub fn gt(strong: bool) -> Self {
    SOrder { strong, ordering: Ordering::Greater }
  }

  pub fn cmp(self, other: Self) -> Self {
    match self {
      SOrder { strong: true, ordering: Ordering::Equal } => other,
      SOrder { strong: false, ordering: Ordering::Equal } => {
        SOrder { strong: false, ordering: other.ordering }
      },
      _ => self,
    }
  }

  #[inline]
  pub fn try_cmp<E, F>(self, other: F) -> Result<Self, E>
  where
    F: FnOnce() -> Result<Self, E>,
  {
    match self {
      SOrder { strong: true, ordering: Ordering::Equal } => other(),
      SOrder { strong: false, ordering: Ordering::Equal } => {
        other().map(|s| SOrder { strong: false, ordering: s.ordering })
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
      ([], []) => Ok(SOrder::eq(true)),
      ([], _) => Ok(SOrder::lt(true)),
      (_, []) => Ok(SOrder::gt(true)),
      ([x, xs_rest @ ..], [y, ys_rest @ ..]) => {
        let result = f(x, y)?;
        match result {
          SOrder { strong: true, ordering: Ordering::Equal } => {
            Self::try_zip(f, xs_rest, ys_rest)
          },
          SOrder { strong: false, ordering: Ordering::Equal } => {
            Self::try_zip(f, xs_rest, ys_rest)
              .map(|s| SOrder { strong: false, ordering: s.ordering })
          },
          _ => Ok(result),
        }
      },
    }
  }
}
