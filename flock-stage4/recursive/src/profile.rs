//! Opt-in wall-time and constraint counts; never changes the verifier graph.
use crate::backend::NativeBuilder;
use serde::Serialize;
use std::{
  sync::{
    OnceLock,
    atomic::{AtomicU64, Ordering},
  },
  time::Instant,
};

#[derive(Clone, Copy, Default, Serialize)]
struct Counts {
  variables: usize,
  arithmetic: usize,
  packing: usize,
  compressions: usize,
  equalities: usize,
}
impl Counts {
  fn read(b: &NativeBuilder) -> Self {
    Self {
      variables: b.graph.variables,
      arithmetic: b.graph.macs.len(),
      packing: b.graph.packs.len(),
      compressions: b.graph.compressions.len(),
      equalities: b.graph.equalities.len(),
    }
  }
  fn delta(self, previous: Self) -> Self {
    Self {
      variables: self.variables - previous.variables,
      arithmetic: self.arithmetic - previous.arithmetic,
      packing: self.packing - previous.packing,
      compressions: self.compressions - previous.compressions,
      equalities: self.equalities - previous.equalities,
    }
  }
}
struct Active {
  id: u64,
  scope: &'static str,
  last: Instant,
  counts: Counts,
  shape_only: Option<bool>,
}
pub(crate) struct Profile(Option<Active>);
impl Profile {
  pub(crate) fn new(scope: &'static str) -> Self {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    static NEXT: AtomicU64 = AtomicU64::new(0);
    Self(
      ENABLED
        .get_or_init(|| {
          std::env::var("IXBY_RECURSION_PROFILE").is_ok_and(|v| v == "1")
        })
        .then(|| Active {
          id: NEXT.fetch_add(1, Ordering::Relaxed),
          scope,
          last: Instant::now(),
          counts: Counts::default(),
          shape_only: None,
        }),
    )
  }
  pub(crate) fn graph(scope: &'static str, b: &NativeBuilder) -> Self {
    let mut profile = Self::new(scope);
    if let Some(active) = &mut profile.0 {
      active.counts = Counts::read(b);
      active.shape_only = Some(b.is_shape_only());
    }
    profile
  }
  pub(crate) fn mark(&mut self, stage: &'static str) {
    self.record(stage, None);
  }
  pub(crate) fn stage(&mut self, stage: &'static str, b: &NativeBuilder) {
    let counts = self.0.as_ref().map(|_| Counts::read(b));
    self.record(stage, counts);
  }
  fn record(&mut self, stage: &'static str, counts: Option<Counts>) {
    let Some(active) = &mut self.0 else { return };
    let seconds = active.last.elapsed().as_secs_f64();
    let delta = counts.map(|now| {
      let delta = now.delta(active.counts);
      active.counts = now;
      delta
    });
    eprintln!(
      "{}",
      serde_json::json!({
        "event": "recursion_profile", "pid": std::process::id(),
        "id": active.id, "scope": active.scope, "stage": stage,
        "shape_only": active.shape_only, "seconds": seconds, "counts": delta,
      })
    );
    active.last = Instant::now();
  }
}
