//! Allocations made and faulted in ahead of use by a background thread.
//!
//! Fresh anonymous memory is zeroed by the kernel on first write, one
//! (transparent huge) page at a time. An execution that grows its record by
//! gigabytes spends a large share of its time in those faults. A store that
//! knows it will need another chunk asks for it here as soon as it starts
//! the current one; the worker allocates it with the global allocator and
//! writes one byte per page, so the faults happen off the executing thread.
//!
//! The worker allocates, so the allocator's own first touch of a fresh block
//! happens there too. It exits once idle, which hands the allocator pages it
//! owns back for reuse and purging when their blocks are freed elsewhere.

use std::alloc::Layout;
use std::sync::mpsc::{self, Receiver, RecvTimeoutError, Sender};
use std::sync::{Arc, Mutex, PoisonError};
use std::time::Duration;

/// Bytes between the writes that fault in an allocation.
const PAGE: usize = 4096;
/// How long the worker waits for a request before exiting.
const IDLE: Duration = Duration::from_millis(250);

enum State {
  Waiting,
  Ready(*mut u8),
  Failed,
  Abandoned,
}

// SAFETY: the pointer is an allocation owned by whoever holds the state's
// lock; it is not shared.
unsafe impl Send for State {}

type Slot = Arc<Mutex<State>>;

struct Job {
  layout: Layout,
  slot: Slot,
}

static WORKER: Mutex<Option<Sender<Job>>> = Mutex::new(None);

fn lock<T>(mutex: &Mutex<T>) -> std::sync::MutexGuard<'_, T> {
  mutex.lock().unwrap_or_else(PoisonError::into_inner)
}

fn submit(job: Job) {
  let mut worker = lock(&WORKER);
  let job = match worker.as_ref() {
    Some(sender) => match sender.send(job) {
      Ok(()) => return,
      Err(mpsc::SendError(job)) => job,
    },
    None => job,
  };
  let (sender, receiver) = mpsc::channel();
  let spawned = std::thread::Builder::new()
    .name("aiur-prefetch".into())
    .spawn(move || work(&receiver));
  if spawned.is_ok() {
    // The receiver lives until the worker exits, which takes this lock.
    let _ = sender.send(job);
    *worker = Some(sender);
  } else {
    *lock(&job.slot) = State::Failed;
  }
}

fn work(receiver: &Receiver<Job>) {
  loop {
    let job = match receiver.recv_timeout(IDLE) {
      Ok(job) => job,
      Err(RecvTimeoutError::Timeout) => {
        // Requests are sent under this lock, so none can arrive between the
        // last check and the worker's removal.
        let mut worker = lock(&WORKER);
        match receiver.try_recv() {
          Ok(job) => {
            drop(worker);
            job
          }
          Err(_) => {
            *worker = None;
            return;
          }
        }
      }
      Err(RecvTimeoutError::Disconnected) => return,
    };
    run(&job);
  }
}

fn run(job: &Job) {
  if matches!(*lock(&job.slot), State::Abandoned) {
    return;
  }
  // SAFETY: the layout has a nonzero size (see `Pending::new`).
  let ptr = unsafe { std::alloc::alloc(job.layout) };
  if !ptr.is_null() {
    for offset in (0..job.layout.size()).step_by(PAGE) {
      // SAFETY: in bounds of the allocation this thread owns; the bytes are
      // uninitialized storage, so writing them changes nothing observable.
      unsafe { ptr.add(offset).write_volatile(0) };
    }
  }
  let mut state = lock(&job.slot);
  match *state {
    State::Abandoned => {
      if !ptr.is_null() {
        // SAFETY: allocated above with this layout and never handed out.
        unsafe { std::alloc::dealloc(ptr, job.layout) };
      }
    }
    _ if ptr.is_null() => *state = State::Failed,
    _ => *state = State::Ready(ptr),
  }
}

/// An allocation of `capacity` values of `T`, requested from the worker.
pub(crate) struct Pending<T> {
  slot: Slot,
  capacity: usize,
  marker: std::marker::PhantomData<T>,
}

impl<T> Pending<T> {
  /// Request `capacity` values of `T` (a nonzero number of bytes).
  pub(crate) fn new(capacity: usize) -> Option<Self> {
    let layout = Layout::array::<T>(capacity).ok()?;
    if layout.size() == 0 {
      return None;
    }
    let slot = Arc::new(Mutex::new(State::Waiting));
    submit(Job { layout, slot: slot.clone() });
    Some(Self { slot, capacity, marker: std::marker::PhantomData })
  }

  pub(crate) fn capacity(&self) -> usize {
    self.capacity
  }

  /// The allocation as an empty vector, if the worker has made it.
  /// `Err(true)` means it never will.
  pub(crate) fn take(&self) -> Result<Vec<T>, bool> {
    let mut state = lock(&self.slot);
    match *state {
      State::Ready(ptr) => {
        *state = State::Abandoned;
        // SAFETY: `ptr` came from the global allocator with
        // `Layout::array::<T>(self.capacity)`, as a vector of this capacity
        // would allocate, and ownership moves to the vector here.
        Ok(unsafe { Vec::from_raw_parts(ptr.cast::<T>(), 0, self.capacity) })
      }
      State::Failed => Err(true),
      _ => Err(false),
    }
  }
}

impl<T> std::fmt::Debug for Pending<T> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("Pending").field("capacity", &self.capacity()).finish()
  }
}

impl<T> Drop for Pending<T> {
  fn drop(&mut self) {
    let mut state = lock(&self.slot);
    if let State::Ready(ptr) = *state
      && let Ok(layout) = Layout::array::<T>(self.capacity)
    {
      // SAFETY: allocated with this layout by the worker and never taken.
      unsafe { std::alloc::dealloc(ptr, layout) };
    }
    *state = State::Abandoned;
  }
}
