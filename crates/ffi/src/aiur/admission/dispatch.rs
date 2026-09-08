//! Bounded completion-driven dispatch, outside the execution Rayon pool.

use super::Admission;
use std::{
  collections::VecDeque,
  panic::{AssertUnwindSafe, catch_unwind},
  sync::mpsc,
};

pub(in crate::aiur) enum Followups<T> {
  Ready(Vec<T>),
  /// Shared-budget exhaustion: stop admission until all outstanding attempts
  /// have returned and released their records/permits, then retry unchanged.
  AfterDrain(T),
}

impl Admission {
  /// `work` must drop its execution record before returning. Only compact
  /// results cross the channel, after the permit is released. Outstanding
  /// tasks AND unconsumed completions together are bounded by pool width.
  /// No admission or channel wait occupies an execution-pool worker.
  pub(in crate::aiur) fn dispatch<T: Send, R: Send>(
    &self,
    pool: &rayon::ThreadPool,
    initial: Vec<T>,
    estimate: impl Fn(&T) -> usize,
    work: impl Fn(&T) -> Result<R, String> + Sync,
    mut complete: impl FnMut(T, R) -> Result<Followups<T>, String>,
  ) -> Result<(), String> {
    if pool.current_thread_index().is_some() {
      return Err(
        "IxVM admission dispatcher must run outside its Rayon pool".into(),
      );
    }
    let width = pool.current_num_threads();
    let (tx, rx) = mpsc::sync_channel::<(T, Result<R, String>)>(width);
    let mut ready = VecDeque::from(initial);
    let mut deferred = VecDeque::new();
    let mut in_flight = 0;
    let mut next_estimate = None;
    pool.in_place_scope(|scope| -> Result<(), String> {
      loop {
        self.check()?;
        // Drain completions before probing the next reservation. A blocked
        // head item must not delay observing failures, splits or released RAM.
        while let Ok((task, result)) = rx.try_recv() {
          in_flight -= 1;
          match complete(task, result?)? {
            Followups::Ready(children) => ready.extend(children),
            Followups::AfterDrain(task) => deferred.push_back(task),
          }
        }
        if in_flight == 0 && !deferred.is_empty() {
          deferred.append(&mut ready);
          std::mem::swap(&mut ready, &mut deferred);
          next_estimate = None;
        }
        if in_flight == 0 && ready.is_empty() {
          return self.check();
        }
        if deferred.is_empty()
          && in_flight < width
          && let Some(next) = ready.front()
          && let Some(permit) = self
            .try_acquire(*next_estimate.get_or_insert_with(|| estimate(next)))?
        {
          let task = ready.pop_front().unwrap();
          next_estimate = None;
          let (work, tx) = (&work, &tx);
          in_flight += 1;
          scope.spawn(move |_| {
            // Under unwind builds, a panic must produce a completion error,
            // not strand the dispatcher waiting for a lost message. Abort/OOM
            // builds still terminate the process; neither yields partial success.
            let result = catch_unwind(AssertUnwindSafe(|| work(&task)))
              .unwrap_or_else(|payload| {
                let message = payload
                  .downcast_ref::<&str>()
                  .copied()
                  .or_else(|| {
                    payload.downcast_ref::<String>().map(String::as_str)
                  })
                  .unwrap_or("non-string panic");
                Err(format!("IxVM shard worker panicked: {message}"))
              });
            if result.is_ok() {
              permit.complete();
            } else {
              drop(permit);
            }
            // At most `width` outstanding messages: even if the coordinator
            // returns an error, scope join cannot strand workers on a full queue.
            let _ = tx.send((task, result));
          });
          continue;
        }
        match rx.recv_timeout(self.shared.options.tick) {
          Ok((task, result)) => {
            in_flight -= 1;
            match complete(task, result?)? {
              Followups::Ready(children) => ready.extend(children),
              Followups::AfterDrain(task) => deferred.push_back(task),
            }
          },
          Err(mpsc::RecvTimeoutError::Timeout) => {},
          Err(mpsc::RecvTimeoutError::Disconnected) => {
            return Err(
              "IxVM completion channel disconnected with unfinished work"
                .into(),
            );
          },
        }
      }
    })?;
    self.check()
  }
}

#[cfg(test)]
mod tests;
