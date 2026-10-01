//! Exact minimum sharing: the canonical construction rule specified in
//! `docs/sharing-minimum.md`.
//!
//! Given a resolved anonymous Constant (or its ordered expanded roots), the
//! optimizer returns the feasible backward-reference sharing encoding with
//! the lexicographically least key
//!
//! ```text
//! K(e) = (L(e), Q(e), bytes(e))
//! ```
//!
//! where `L` is the byte length of the complete serialized Constant, `Q` the
//! vector of structural term IDs (§3.2) of the table entries in stored order
//! and `bytes` the serialized Constant. All non-sharing fields, root order and
//! the refs/univs tables are fixed; only the table sequence and per-occurrence
//! inline/reference choices vary. A table entry may reference only earlier
//! entries (the backward-reference class of §3.1); this module does not claim
//! optimality over forward-acyclic tables.
//!
//! Structure:
//! - [`SharingDag`]: collision-independent hash-consing of the expanded roots
//!   with §3.2 structural IDs, built from expanded roots or by bounded,
//!   validated expansion of an existing table.
//! - `dict`: the fixed-dictionary recurrence `C_M` (§5) with explicit
//!   telescope cuts, and byte-least materialization.
//! - `search`: the sparse width-state dynamic program (§6) with the proved
//!   reductions R1/R2, the optimistic-dictionary lower bound (§4.1) and a
//!   materialization lower bound.
//!
//! Every limit in [`ExactSharingLimits`] is enforced with deterministic
//! counters; exhausting one returns [`SharingError::ResourceExhausted`] and
//! never a best-so-far encoding. Lengths use checked arithmetic or the exact
//! overflow sentinel [`Len`].
//!
//! # Pinned interpretations
//!
//! These choices are part of the canonical result and must match any other
//! implementation of the rule:
//!
//! - **ID domain.** Structural IDs number exactly the distinct subterms
//!   reachable from the ordered roots after expansion. Entries of an
//!   incoming table that no root reaches are validated but do not receive
//!   IDs, so they cannot influence `Q`.
//! - **Admission.** Expansion accepts only the backward-reference class:
//!   a Share in entry `i` must name an entry `< i`, a Share in a root must
//!   name an entry `< len`. Out-of-range, forward and cyclic references are
//!   [`MalformedSharing`] errors, including in unreachable entries.
//!   [`optimize_sharing`] rejects any Share leaf in its input.
//! - **Byte tie.** For a fixed table sequence each entry and root is
//!   materialized as its byte-least minimum-length representation. This
//!   equals the rule: an inline constructor precedes a Share of the same
//!   length (flags `0x0..=0xA` < `0xB`); among telescope prefixes of one
//!   node the least Tag4 header bytes win (distinct prefix lengths always
//!   differ inside the header); then children independently.
//! - **Variable length.** [`ExactSharingResult::variable_len`] is the sum of
//!   the root encodings, the table's Tag0 count and the entry encodings; the
//!   rest of the Constant is fixed and checked against `Constant::put`.
//!
//! Pruning (the §4.1 bound strengthened with `share_width(k)` for future
//! entries, the materialization bound, and the heuristic and greedy upper
//! bound seeds) never changes a successful result, only which inputs finish
//! within the limits; `search` documents the proofs.

mod cost;
mod dag;
mod dict;
mod roots;
mod search;
mod uniform;

#[cfg(test)]
mod oracle;
#[cfg(test)]
mod tests;

use std::fmt;
use std::sync::Arc;

pub use cost::{
  Len, byte_count, constant_fixed_len, constant_len, expr_len, share_width,
  sharing_table_len, tag0_len, tag4_len,
};
pub use dag::{Children, Node, NodeKey, SharingDag, TermId};
pub use dict::{FixedDictionary, dictionary_cost, materialize_with_dictionary};
pub use roots::{
  constant_info_root_count, constant_info_root_exprs, rebuild_constant_info,
};
pub use search::{
  candidate_terms, optimize_sharing_uniform_reference, sequence_len,
};
pub use uniform::{
  UniformClass, UniformSharingResult, normalize_constant_sharing_uniform,
  optimize_dag_uniform, optimize_sharing_uniform,
};

use crate::constant::Constant;
use crate::expr::Expr;

/// Deterministic resource limits and search options. Exhausting a limit is
/// an error. Limits and the pruning options can change success into failure
/// but never the bytes of a success.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactSharingLimits {
  /// Pointer-distinct input expression nodes visited during expansion.
  pub max_input_nodes: u64,
  /// Distinct structural nodes interned (including unreachable entries).
  pub max_distinct_nodes: u64,
  /// Maximum height of the expanded DAG.
  pub max_height: u64,
  /// Sharing candidates remaining after reductions R1/R2.
  pub max_candidates: u64,
  /// Width states created by the dynamic program.
  pub max_states: u64,
  /// States in one layer (entries stored) of the dynamic program.
  pub max_layer_states: u64,
  /// Candidate transitions examined.
  pub max_transitions: u64,
  /// Node evaluations, spine steps and marking steps.
  pub max_work: u64,
  /// Length of the complete serialized output.
  pub max_output_bytes: u64,
  /// Seed the upper bound with the historical heuristic when it is safely
  /// representable. Affects pruning only.
  pub heuristic_upper_bound: bool,
  /// Prune states by proved lower bounds. Disabling it explores every
  /// reachable width state (a reference mode for tests).
  pub lower_bound_pruning: bool,
  /// Seed the upper bound with a deterministic greedy table sequence.
  /// Affects pruning only.
  pub greedy_upper_bound: bool,
  /// Also prune by the materialization bound (see `search`), in addition to
  /// the §4.1 dictionary bound.
  pub materialization_bound: bool,
}

impl Default for ExactSharingLimits {
  fn default() -> Self {
    ExactSharingLimits {
      max_input_nodes: 1 << 26,
      max_distinct_nodes: 1 << 24,
      max_height: 1 << 24,
      max_candidates: 1 << 16,
      max_states: 1 << 20,
      max_layer_states: 1 << 18,
      max_transitions: 1 << 28,
      max_work: 1 << 36,
      max_output_bytes: 1 << 32,
      heuristic_upper_bound: true,
      greedy_upper_bound: true,
      lower_bound_pruning: true,
      materialization_bound: true,
    }
  }
}

impl ExactSharingLimits {
  /// No limits except those of the representation itself.
  pub fn unbounded() -> Self {
    ExactSharingLimits {
      max_input_nodes: u64::MAX,
      max_distinct_nodes: u64::MAX,
      max_height: u64::MAX,
      max_candidates: u64::MAX,
      max_states: u64::MAX,
      max_layer_states: u64::MAX,
      max_transitions: u64::MAX,
      max_work: u64::MAX,
      max_output_bytes: u64::MAX,
      ..Self::default()
    }
  }
}

/// Non-semantic statistics of one invocation.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ExactSharingStats {
  pub input_nodes: u64,
  pub distinct_nodes: u64,
  pub height: u64,
  pub candidates: u64,
  pub states_created: u64,
  pub states_expanded: u64,
  pub states_pruned: u64,
  pub transitions: u64,
  pub max_layer: u64,
  pub layers: u64,
  pub work: u64,
  /// Variable length of the historical heuristic, when it was evaluated.
  pub heuristic_len: Option<u64>,
  /// Variable length of the greedy seed, when it was computed.
  pub greedy_len: Option<u64>,
  /// Variable length of the unshared encoding (`None` if it overflows).
  pub unshared_len: Option<u64>,
}

/// Where a Share reference occurred.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ShareLocation {
  Entry(u64),
  Root(u64),
}

/// The input is not a valid backward-reference sharing encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MalformedSharing {
  /// A Share index is not below the table length.
  ShareOutOfRange { location: ShareLocation, index: u64, table_len: u64 },
  /// Entry `entry` references a later entry without closing a cycle.
  ForwardShare { entry: u64, index: u64 },
  /// Entry `entry` references `index >= entry` and that closes a cycle.
  CyclicShare { entry: u64, index: u64 },
  /// A Share leaf in input that must already be expanded.
  UnresolvedShare { root: u64, index: u64 },
  /// Reassembly did not consume exactly the ConstantInfo's roots.
  RootCountMismatch { expected: u64, actual: u64 },
}

/// A value exceeds a representable index or length domain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FormatBound {
  /// More distinct terms than the `u32` term-ID space.
  TermIdSpace { nodes: u64 },
  /// A serialized length reaches `u64::MAX`.
  LengthOverflow,
  /// A uniform Share width outside `1..=255`.
  UniformWidth { w: u64 },
}

/// Which deterministic limit was exhausted.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Resource {
  InputNodes,
  DistinctNodes,
  Height,
  Candidates,
  States,
  LayerStates,
  Transitions,
  Work,
  OutputBytes,
}

/// A deterministic resource limit was reached before certification.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ResourceExhausted {
  pub resource: Resource,
  pub limit: u64,
}

/// Failure of an exact-sharing operation. No variant carries a partial or
/// uncertified encoding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SharingError {
  Malformed(MalformedSharing),
  FormatBound(FormatBound),
  ResourceExhausted(ResourceExhausted),
  /// An internal invariant failed; this is a bug, reported instead of a
  /// wrong answer.
  Internal(String),
}

impl fmt::Display for SharingError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      SharingError::Malformed(m) => write!(f, "malformed sharing: {m:?}"),
      SharingError::FormatBound(b) => write!(f, "format bound: {b:?}"),
      SharingError::ResourceExhausted(r) => {
        write!(f, "resource exhausted: {:?} (limit {})", r.resource, r.limit)
      },
      SharingError::Internal(s) => write!(f, "internal error: {s}"),
    }
  }
}

impl std::error::Error for SharingError {}

/// Deterministic work accounting against [`ExactSharingLimits`].
pub(crate) struct Meter<'l> {
  limits: &'l ExactSharingLimits,
  pub(crate) stats: ExactSharingStats,
}

impl<'l> Meter<'l> {
  pub(crate) fn new(limits: &'l ExactSharingLimits) -> Self {
    Meter { limits, stats: ExactSharingStats::default() }
  }

  pub(crate) fn limits(&self) -> &'l ExactSharingLimits {
    self.limits
  }

  fn exhausted(resource: Resource, limit: u64) -> SharingError {
    SharingError::ResourceExhausted(ResourceExhausted { resource, limit })
  }

  pub(crate) fn input_node(&mut self) -> Result<(), SharingError> {
    self.stats.input_nodes = self.stats.input_nodes.saturating_add(1);
    if self.stats.input_nodes > self.limits.max_input_nodes {
      return Err(Self::exhausted(
        Resource::InputNodes,
        self.limits.max_input_nodes,
      ));
    }
    Ok(())
  }

  pub(crate) fn distinct_nodes(&mut self, n: u64) -> Result<(), SharingError> {
    self.stats.distinct_nodes = self.stats.distinct_nodes.max(n);
    if n > self.limits.max_distinct_nodes {
      return Err(Self::exhausted(
        Resource::DistinctNodes,
        self.limits.max_distinct_nodes,
      ));
    }
    Ok(())
  }

  pub(crate) fn height(&mut self, h: u64) -> Result<(), SharingError> {
    self.stats.height = self.stats.height.max(h);
    if h > self.limits.max_height {
      return Err(Self::exhausted(Resource::Height, self.limits.max_height));
    }
    Ok(())
  }

  pub(crate) fn candidates(&mut self, k: u64) -> Result<(), SharingError> {
    self.stats.candidates = k;
    if k > self.limits.max_candidates {
      return Err(Self::exhausted(
        Resource::Candidates,
        self.limits.max_candidates,
      ));
    }
    Ok(())
  }

  pub(crate) fn work(&mut self, n: u64) -> Result<(), SharingError> {
    self.stats.work = self.stats.work.saturating_add(n);
    if self.stats.work > self.limits.max_work {
      return Err(Self::exhausted(Resource::Work, self.limits.max_work));
    }
    Ok(())
  }

  pub(crate) fn state(&mut self) -> Result<(), SharingError> {
    self.stats.states_created = self.stats.states_created.saturating_add(1);
    if self.stats.states_created > self.limits.max_states {
      return Err(Self::exhausted(Resource::States, self.limits.max_states));
    }
    Ok(())
  }

  pub(crate) fn transition(&mut self) -> Result<(), SharingError> {
    self.stats.transitions = self.stats.transitions.saturating_add(1);
    if self.stats.transitions > self.limits.max_transitions {
      return Err(Self::exhausted(
        Resource::Transitions,
        self.limits.max_transitions,
      ));
    }
    Ok(())
  }

  pub(crate) fn layer(&mut self, size: u64) -> Result<(), SharingError> {
    self.stats.max_layer = self.stats.max_layer.max(size);
    if size > self.limits.max_layer_states {
      return Err(Self::exhausted(
        Resource::LayerStates,
        self.limits.max_layer_states,
      ));
    }
    Ok(())
  }

  pub(crate) fn output(&mut self, len: u64) -> Result<(), SharingError> {
    if len > self.limits.max_output_bytes {
      return Err(Self::exhausted(
        Resource::OutputBytes,
        self.limits.max_output_bytes,
      ));
    }
    Ok(())
  }
}

/// A certified exact-minimum sharing encoding of ordered expanded roots.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExactSharingResult {
  /// Rewritten roots, in input order.
  pub roots: Vec<Arc<Expr>>,
  /// The sharing table; entry `i` references only entries `< i`.
  pub sharing: Vec<Arc<Expr>>,
  /// `Q`: structural term ID of each table entry, in stored order.
  pub table_terms: Vec<TermId>,
  /// Exact variable bytes: roots + table Tag0 count + table entries.
  pub variable_len: u64,
  /// Nonsemantic statistics.
  pub stats: ExactSharingStats,
}

/// Exact minimum sharing of ordered, fully expanded roots (no Share leaves).
///
/// The full-Constant key differs from the variable length only by bytes that
/// do not depend on sharing, so the result is the canonical encoding of any
/// Constant with these ordered roots.
pub fn optimize_sharing(
  roots: &[Arc<Expr>],
  limits: &ExactSharingLimits,
) -> Result<ExactSharingResult, SharingError> {
  let mut meter = Meter::new(limits);
  let dag = SharingDag::build(roots, None, &mut meter)?;
  search::optimize(&dag, 0, &mut meter)
}

/// [`optimize_sharing`] on an already built DAG.
pub fn optimize_dag(
  dag: &SharingDag,
  limits: &ExactSharingLimits,
) -> Result<ExactSharingResult, SharingError> {
  let mut meter = Meter::new(limits);
  search::optimize(dag, 0, &mut meter)
}

/// Expand `c`'s table (validating backward references) and return the
/// canonical exact-minimum Constant together with its search result.
pub fn normalize_constant_sharing_with_stats(
  c: &Constant,
  limits: &ExactSharingLimits,
) -> Result<(Constant, ExactSharingResult), SharingError> {
  let mut meter = Meter::new(limits);
  let roots = constant_info_root_exprs(&c.info);
  let dag = SharingDag::build(&roots, Some(&c.sharing), &mut meter)?;
  let fixed = constant_fixed_len(c)
    .ok_or(SharingError::FormatBound(FormatBound::LengthOverflow))?;
  let result = search::optimize(&dag, fixed, &mut meter)?;
  let info = rebuild_constant_info(&c.info, &result.roots)?;
  let out = Constant {
    info,
    sharing: result.sharing.clone(),
    refs: c.refs.clone(),
    univs: c.univs.clone(),
  };
  // Fixed-cost accounting: the real serializer must agree with the
  // decomposition the search optimized.
  let mut bytes = Vec::new();
  out.put(&mut bytes);
  let expected = fixed.checked_add(result.variable_len);
  if u64::try_from(bytes.len()).ok() != expected {
    return Err(SharingError::Internal(format!(
      "serialized length {} differs from fixed {fixed} + variable {}",
      bytes.len(),
      result.variable_len
    )));
  }
  Ok((out, result))
}

/// Expand `c`'s table and return its canonical exact-minimum encoding.
pub fn normalize_constant_sharing(
  c: &Constant,
  limits: &ExactSharingLimits,
) -> Result<Constant, SharingError> {
  normalize_constant_sharing_with_stats(c, limits).map(|(c, _)| c)
}

/// Outcome of [`check_canonical_sharing`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CanonicalCheck {
  Canonical,
  NonCanonical { expected: Box<Constant> },
}

/// Whether `c` is byte-identical to its canonical exact-minimum encoding.
pub fn check_canonical_sharing(
  c: &Constant,
  limits: &ExactSharingLimits,
) -> Result<CanonicalCheck, SharingError> {
  let expected = normalize_constant_sharing(c, limits)?;
  let mut have = Vec::new();
  c.put(&mut have);
  let mut want = Vec::new();
  expected.put(&mut want);
  Ok(if have == want {
    CanonicalCheck::Canonical
  } else {
    CanonicalCheck::NonCanonical { expected: Box::new(expected) }
  })
}

/// Failure of [`normalize_constant_bytes`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NormalizeBytesError {
  /// The input is not exactly one wire-valid serialized Constant.
  Decode(String),
  Sharing(SharingError),
}

impl fmt::Display for NormalizeBytesError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      NormalizeBytesError::Decode(e) => write!(f, "decode: {e}"),
      NormalizeBytesError::Sharing(e) => write!(f, "{e}"),
    }
  }
}

impl std::error::Error for NormalizeBytesError {}

/// Byte-level normalization: decode exactly one serialized Constant (no
/// trailing bytes), expand and validate its table, and return the serialized
/// canonical exact-minimum Constant.
pub fn normalize_constant_bytes(
  bytes: &[u8],
  limits: &ExactSharingLimits,
) -> Result<Vec<u8>, NormalizeBytesError> {
  let mut input = bytes;
  let c = Constant::get(&mut input).map_err(NormalizeBytesError::Decode)?;
  if !input.is_empty() {
    return Err(NormalizeBytesError::Decode(format!(
      "{} trailing bytes after the Constant",
      input.len()
    )));
  }
  let out = normalize_constant_sharing(&c, limits)
    .map_err(NormalizeBytesError::Sharing)?;
  let mut buf = Vec::new();
  out.put(&mut buf);
  Ok(buf)
}

/// Byte-level uniform-width normalization: decode exactly one serialized
/// Constant, re-share it with the uniform-width optimum for Share width `w`,
/// and return the serialized result.
pub fn normalize_constant_bytes_uniform(
  w: u64,
  bytes: &[u8],
  limits: &ExactSharingLimits,
) -> Result<Vec<u8>, NormalizeBytesError> {
  let mut input = bytes;
  let c = Constant::get(&mut input).map_err(NormalizeBytesError::Decode)?;
  if !input.is_empty() {
    return Err(NormalizeBytesError::Decode(format!(
      "{} trailing bytes after the Constant",
      input.len()
    )));
  }
  let (out, _) = normalize_constant_sharing_uniform(w, &c, limits)
    .map_err(NormalizeBytesError::Sharing)?;
  let mut buf = Vec::new();
  out.put(&mut buf);
  Ok(buf)
}
