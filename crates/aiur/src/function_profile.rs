//! Optional bytecode-function timing, independent of the host call stack.
//!
//! Arguments are marshalled by the caller. Callee time includes the memo
//! lookup, frame setup, body, query insertion and copying results back. Native
//! operations, static maps and hints stay in their enclosing function's time.
//! Profiler bookkeeping is outside timed spans; clock calls and perturbations
//! to caches/code layout still affect measurements. Compare an uninstrumented
//! build before interpreting small differences. Inclusive totals double-count
//! nested calls (including recursion); self totals do not.
use std::time::Instant;

#[derive(Clone, Debug, Default)]
pub struct FunctionTiming {
  pub calls: u64,
  pub cache_hits: u64,
  pub self_ns: u64,
  pub inclusive_ns: u64,
  pub cached_ns: u64,
}

struct Active {
  function: usize,
  self_ns: u64,
  children_ns: u64,
}

pub struct FunctionProfiler {
  pub functions: Vec<FunctionTiming>,
  /// Count actual interpreter dispatches in a separate diagnostic build.
  /// These counters perturb execution; do not use that build for timings.
  #[cfg(feature = "function-profile-ops")]
  pub operations: Vec<std::collections::BTreeMap<&'static str, u64>>,
  stack: Vec<Active>,
  resumed: Option<Instant>,
}

impl FunctionProfiler {
  pub fn new(functions: usize) -> Self {
    Self {
      functions: vec![FunctionTiming::default(); functions],
      #[cfg(feature = "function-profile-ops")]
      operations: vec![std::collections::BTreeMap::new(); functions],
      stack: Vec::new(),
      resumed: None,
    }
  }

  fn pause(&mut self, now: Instant) {
    if let Some(resumed) = self.resumed.take() {
      self.stack.last_mut().unwrap().self_ns +=
        now.duration_since(resumed).as_nanos() as u64;
    }
  }

  pub(crate) fn enter(&mut self, function: usize) {
    self.pause(Instant::now());
    self.functions[function].calls += 1;
    self.stack.push(Active { function, self_ns: 0, children_ns: 0 });
    self.resumed = Some(Instant::now());
  }

  pub(crate) fn exit(&mut self, cache_hit: bool) {
    self.pause(Instant::now());
    let frame = self.stack.pop().unwrap();
    let inclusive = frame.self_ns + frame.children_ns;
    let timing = &mut self.functions[frame.function];
    timing.self_ns += frame.self_ns;
    timing.inclusive_ns += inclusive;
    if cache_hit {
      timing.cache_hits += 1;
      timing.cached_ns += frame.self_ns;
    }
    if let Some(parent) = self.stack.last_mut() {
      parent.children_ns += inclusive;
      self.resumed = Some(Instant::now());
    }
  }

  #[cfg(feature = "function-profile-ops")]
  pub(crate) fn operation(&mut self, name: &'static str) {
    let function = self.stack.last().unwrap().function;
    *self.operations[function].entry(name).or_default() += 1;
  }

  /// Whether all entered calls returned. Discard timings if execution failed.
  pub fn is_complete(&self) -> bool {
    self.stack.is_empty()
  }
}
