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
  pub fn weak_cmp<A: Ord>(x: &A, y: &A) -> Self {
    SOrd { strong: false, ordering: x.cmp(y) }
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

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn eq_strong_then_lt() {
    let result = SOrd::eq(true).compare(SOrd::lt(true));
    assert_eq!(result.ordering, Ordering::Less);
    assert!(result.strong);
  }

  #[test]
  fn eq_strong_then_gt() {
    let result = SOrd::eq(true).compare(SOrd::gt(false));
    assert_eq!(result.ordering, Ordering::Greater);
    assert!(!result.strong);
  }

  #[test]
  fn eq_strong_then_eq() {
    let result = SOrd::eq(true).compare(SOrd::eq(true));
    assert_eq!(result.ordering, Ordering::Equal);
    assert!(result.strong);
  }

  #[test]
  fn eq_weak_then_lt() {
    let result = SOrd::eq(false).compare(SOrd::lt(true));
    assert_eq!(result.ordering, Ordering::Less);
    assert!(!result.strong); // weak propagates
  }

  #[test]
  fn eq_weak_then_eq() {
    let result = SOrd::eq(false).compare(SOrd::eq(true));
    assert_eq!(result.ordering, Ordering::Equal);
    assert!(!result.strong); // weak propagates
  }

  #[test]
  fn lt_strong_short_circuits() {
    let result = SOrd::lt(true).compare(SOrd::gt(true));
    assert_eq!(result.ordering, Ordering::Less);
    assert!(result.strong);
  }

  #[test]
  fn gt_strong_short_circuits() {
    let result = SOrd::gt(true).compare(SOrd::lt(true));
    assert_eq!(result.ordering, Ordering::Greater);
    assert!(result.strong);
  }

  #[test]
  fn lt_weak_short_circuits() {
    let result = SOrd::lt(false).compare(SOrd::gt(true));
    assert_eq!(result.ordering, Ordering::Less);
    assert!(!result.strong);
  }

  #[test]
  fn try_compare_eq_strong_calls_closure() {
    let mut called = false;
    let result: Result<SOrd, ()> = SOrd::eq(true).try_compare(|| {
      called = true;
      Ok(SOrd::lt(true))
    });
    assert!(called);
    assert_eq!(result.unwrap().ordering, Ordering::Less);
  }

  #[test]
  fn try_compare_lt_does_not_call_closure() {
    let mut called = false;
    let result: Result<SOrd, ()> = SOrd::lt(true).try_compare(|| {
      called = true;
      Ok(SOrd::gt(true))
    });
    assert!(!called);
    assert_eq!(result.unwrap().ordering, Ordering::Less);
  }

  #[test]
  fn try_compare_eq_weak_propagates() {
    let result: Result<SOrd, ()> =
      SOrd::eq(false).try_compare(|| Ok(SOrd::lt(true)));
    let r = result.unwrap();
    assert_eq!(r.ordering, Ordering::Less);
    assert!(!r.strong); // weak propagates
  }

  #[test]
  fn try_zip_both_empty() {
    let result: Result<SOrd, ()> =
      SOrd::try_zip(|x: &i32, y: &i32| Ok(SOrd::cmp(x, y)), &[], &[]);
    let r = result.unwrap();
    assert_eq!(r.ordering, Ordering::Equal);
    assert!(r.strong);
  }

  #[test]
  fn try_zip_left_shorter() {
    let result: Result<SOrd, ()> =
      SOrd::try_zip(|x: &i32, y: &i32| Ok(SOrd::cmp(x, y)), &[], &[1]);
    assert_eq!(result.unwrap().ordering, Ordering::Less);
  }

  #[test]
  fn try_zip_right_shorter() {
    let result: Result<SOrd, ()> =
      SOrd::try_zip(|x: &i32, y: &i32| Ok(SOrd::cmp(x, y)), &[1], &[]);
    assert_eq!(result.unwrap().ordering, Ordering::Greater);
  }

  #[test]
  fn try_zip_equal_elements() {
    let result: Result<SOrd, ()> = SOrd::try_zip(
      |x: &i32, y: &i32| Ok(SOrd::cmp(x, y)),
      &[1, 2, 3],
      &[1, 2, 3],
    );
    let r = result.unwrap();
    assert_eq!(r.ordering, Ordering::Equal);
    assert!(r.strong);
  }

  #[test]
  fn try_zip_first_difference() {
    let mut count = 0;
    let result: Result<SOrd, ()> = SOrd::try_zip(
      |x: &i32, y: &i32| {
        count += 1;
        Ok(SOrd::cmp(x, y))
      },
      &[1, 5, 3],
      &[1, 2, 3],
    );
    assert_eq!(result.unwrap().ordering, Ordering::Greater);
    assert_eq!(count, 2); // stops after finding the difference at index 1
  }

  #[test]
  fn try_zip_weak_propagation() {
    let result: Result<SOrd, ()> = SOrd::try_zip(
      |x: &i32, y: &i32| Ok(SOrd::weak_cmp(x, y)),
      &[1, 2],
      &[1, 2],
    );
    let r = result.unwrap();
    assert_eq!(r.ordering, Ordering::Equal);
    assert!(!r.strong); // weak propagates through the chain
  }
}
