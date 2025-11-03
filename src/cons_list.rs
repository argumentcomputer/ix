use std::sync::Arc;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum ConsList<T> {
    Nil,
    Cons(T, Arc<ConsList<T>>, usize),
}

struct ConsListIter<'a, T>(&'a ConsList<T>);
impl<'a, T> Iterator for ConsListIter<'a, T> {
    type Item = &'a T;
    fn next(&mut self) -> Option<Self::Item> {
        match &self.0 {
            ConsList::Nil => None,
            ConsList::Cons(t, tail, _) => {
                self.0 = tail;
                Some(t)
            }
        }
    }
}

impl<T> ConsList<T> {
    #[inline]
    pub fn cons(&self, t: T) -> Self
    where
        T: Clone,
    {
        match self {
            Self::Nil => Self::Cons(t, Arc::new(Self::Nil), 1),
            Self::Cons(.., len) => Self::Cons(t, Arc::new(self.clone()), len + 1),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        match self {
            Self::Nil => 0,
            Self::Cons(.., len) => *len,
        }
    }

    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        ConsListIter(self)
    }

    pub fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self
    where
        T: Clone,
        <I as IntoIterator>::IntoIter: DoubleEndedIterator,
    {
        iter.into_iter().rev().fold(Self::Nil, |acc, t| acc.cons(t))
    }

    #[inline]
    pub fn contains(&self, t: &T) -> bool
    where
        T: PartialEq,
    {
        self.iter().any(|x| x == t)
    }

    #[inline]
    pub fn index_of(&self, t: &T) -> Option<usize>
    where
        T: PartialEq,
    {
        self.iter().position(|x| x == t)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_list_len_and_iter() {
        let list: ConsList<i32> = ConsList::Nil;
        assert_eq!(list.len(), 0);
        assert_eq!(list.iter().count(), 0);
        assert!(list.iter().next().is_none());
    }

    #[test]
    fn test_single_element_list() {
        let list = ConsList::Nil.cons(10);
        assert_eq!(list.len(), 1);

        let collected: Vec<_> = list.iter().cloned().collect();
        assert_eq!(collected, vec![10]);
    }

    #[test]
    fn test_multiple_elements_list() {
        let list = ConsList::Nil.cons(3).cons(2).cons(1);
        assert_eq!(list.len(), 3);

        // The elements are stored in cons order (head-first)
        let collected: Vec<_> = list.iter().cloned().collect();
        assert_eq!(collected, vec![1, 2, 3]);
    }

    #[test]
    fn test_from_iter() {
        let vec = vec![1, 2, 3];
        let list = ConsList::from_iter(vec.clone());
        assert_eq!(list.len(), 3);

        let collected: Vec<_> = list.iter().cloned().collect();
        assert_eq!(collected, vec);
    }

    #[test]
    fn test_contains() {
        let list = ConsList::from_iter(vec![10, 20, 30]);

        assert!(list.contains(&10));
        assert!(list.contains(&30));
        assert!(!list.contains(&99));
    }

    #[test]
    fn test_index_of() {
        let list = ConsList::from_iter(vec![10, 20, 30]);

        assert_eq!(list.index_of(&10), Some(0));
        assert_eq!(list.index_of(&30), Some(2));
        assert_eq!(list.index_of(&99), None);
    }

    #[test]
    fn test_iter_mutation_order() {
        // Ensure iterator traverses the list without altering it
        let list = ConsList::from_iter(vec![1, 2, 3]);
        let mut iter = list.iter();

        assert_eq!(iter.next(), Some(&1));
        assert_eq!(iter.next(), Some(&2));
        assert_eq!(iter.next(), Some(&3));
        assert_eq!(iter.next(), None);

        // The original list should remain unchanged
        let collected: Vec<_> = list.iter().cloned().collect();
        assert_eq!(collected, vec![1, 2, 3]);
    }

    #[test]
    fn test_clone_and_eq() {
        let list1 = ConsList::from_iter(vec![1, 2, 3]);
        let list2 = list1.clone();
        assert_eq!(list1, list2);

        let different = ConsList::from_iter(vec![1, 2]);
        assert_ne!(list1, different);
    }

    #[test]
    fn test_cons_increases_length() {
        let mut list = ConsList::Nil;
        for i in 0..5 {
            list = list.cons(i);
            assert_eq!(list.len(), i + 1);
        }

        let collected: Vec<_> = list.iter().cloned().collect();
        assert_eq!(collected, vec![4, 3, 2, 1, 0]);
    }

    #[test]
    fn test_with_strings() {
        let list = ConsList::from_iter(vec!["a", "b"]);
        assert!(list.contains(&"a"));
        assert!(!list.contains(&"c"));

        let collected: Vec<_> = list.iter().cloned().collect();
        assert_eq!(collected, vec!["a", "b"]);
    }
}
