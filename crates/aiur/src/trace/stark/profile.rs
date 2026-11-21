//! Optional wall-clock diagnostics, compiled out of ordinary trace generation.
//! Circuit spans overlap under Rayon and must not be summed as wall time.
use std::{
  sync::Mutex,
  time::{Duration, Instant},
};

/// Time adapter work around the cryptographic prover separately from row
/// generation. In particular, batch lookup reconstruction is not part of the
/// fused `generate` measurement.
pub(super) struct Span {
  phase: &'static str,
  start: Instant,
  cells: usize,
}

impl Span {
  pub(super) fn new(phase: &'static str, cells: usize) -> Self {
    Self { phase, start: Instant::now(), cells }
  }
}

impl Drop for Span {
  fn drop(&mut self) {
    eprintln!(
      "{}",
      serde_json::json!({"event": "aiur_prover_profile", "phase": self.phase,
        "elapsed_seconds": self.start.elapsed().as_secs_f64(), "cells": self.cells})
    );
  }
}

pub(super) struct Phases {
  start: Instant,
  last: Instant,
  phases: Vec<(&'static str, f64)>,
  circuits: Mutex<Vec<(usize, f64)>>,
}

impl Phases {
  pub(super) fn new() -> Self {
    let start = Instant::now();
    Self { start, last: start, phases: vec![], circuits: Mutex::new(vec![]) }
  }

  pub(super) fn mark(&mut self, name: &'static str) {
    let now = Instant::now();
    self.phases.push((name, (now - self.last).as_secs_f64()));
    self.last = now;
  }

  pub(super) fn circuit(&self, index: usize, elapsed: Duration) {
    self.circuits.lock().unwrap().push((index, elapsed.as_secs_f64()));
  }

  pub(super) fn finish(self, names: &[String], lookups: bool) {
    let elapsed = self.start.elapsed().as_secs_f64();
    let mut circuits = self.circuits.into_inner().unwrap();
    circuits.sort_unstable_by_key(|(i, _)| *i);
    let circuits: Vec<_> =
      circuits.into_iter().map(|(i, seconds)| (&names[i], seconds)).collect();
    eprintln!(
      "{}",
      serde_json::json!({"event": "aiur_trace_profile", "host_lookups": lookups,
        "elapsed_seconds": elapsed, "phases": self.phases, "circuits": circuits})
    );
  }
}
