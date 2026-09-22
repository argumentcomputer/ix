use std::collections::VecDeque;
use std::sync::{Condvar, Mutex};

struct State<T> {
  priority: VecDeque<T>,
  ordinary: VecDeque<T>,
  closed: bool,
}

/// Bounded ownership transfer with ready joins ahead of claims.
pub(super) struct WorkQueue<T> {
  capacity: usize,
  state: Mutex<State<T>>,
  changed: Condvar,
}

impl<T> WorkQueue<T> {
  pub(super) fn new(capacity: usize) -> Self {
    assert!(capacity > 0);
    Self {
      capacity,
      state: Mutex::new(State {
        priority: VecDeque::new(),
        ordinary: VecDeque::new(),
        closed: false,
      }),
      changed: Condvar::new(),
    }
  }

  pub(super) fn push(&self, item: T, priority: bool) -> Result<(), T> {
    let mut state = self.state.lock().unwrap();
    while !state.closed
      && state.priority.len() + state.ordinary.len() == self.capacity
    {
      state = self.changed.wait(state).unwrap();
    }
    if state.closed {
      return Err(item);
    }
    if priority {
      state.priority.push_back(item);
    } else {
      state.ordinary.push_back(item);
    }
    self.changed.notify_all();
    Ok(())
  }

  pub(super) fn pop(&self) -> Option<T> {
    let mut state = self.state.lock().unwrap();
    loop {
      if state.closed {
        return None;
      }
      if let Some(item) =
        state.priority.pop_front().or_else(|| state.ordinary.pop_front())
      {
        self.changed.notify_all();
        return Some(item);
      }
      state = self.changed.wait(state).unwrap();
    }
  }

  pub(super) fn close(&self) {
    let mut state = self.state.lock().unwrap();
    state.closed = true;
    let priority = std::mem::take(&mut state.priority);
    let ordinary = std::mem::take(&mut state.ordinary);
    self.changed.notify_all();
    drop(state);
    drop((priority, ordinary));
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::{
    sync::{Arc, mpsc},
    thread,
    time::Duration,
  };

  #[test]
  fn ready_joins_precede_claims_without_reordering_peers() {
    let queue = WorkQueue::new(4);
    queue.push(1, false).unwrap();
    queue.push(2, true).unwrap();
    queue.push(3, true).unwrap();
    queue.push(4, false).unwrap();
    assert_eq!(
      (queue.pop(), queue.pop(), queue.pop(), queue.pop()),
      (Some(2), Some(3), Some(1), Some(4))
    );
  }

  #[test]
  fn closing_releases_items_and_wakes_producers_and_consumers() {
    let full = Arc::new(WorkQueue::new(1));
    let stored = Arc::new(());
    full.push(Arc::clone(&stored), false).unwrap();
    let producer_queue = Arc::clone(&full);
    let (tx, rx) = mpsc::channel();
    let producer = thread::spawn(move || {
      tx.send(producer_queue.push(Arc::new(()), false).is_err()).unwrap();
    });
    full.close();
    assert_eq!(Arc::strong_count(&stored), 1);
    assert!(rx.recv_timeout(Duration::from_secs(3)).unwrap());
    producer.join().unwrap();
    assert!(full.pop().is_none());

    let empty = Arc::new(WorkQueue::<usize>::new(1));
    let consumer_queue = Arc::clone(&empty);
    let (tx, rx) = mpsc::channel();
    let consumer =
      thread::spawn(move || tx.send(consumer_queue.pop()).unwrap());
    empty.close();
    assert_eq!(rx.recv_timeout(Duration::from_secs(3)).unwrap(), None);
    consumer.join().unwrap();
  }
}
