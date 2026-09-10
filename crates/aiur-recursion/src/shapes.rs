//! The pinned recursion shapes: the per-chip row counts every leaf proof and
//! every compress-level proof is padded to, so that each level of the
//! pipeline sees exactly one proof shape and the programs above the leaves
//! — compose, shrink, wrap, the gnark circuit — are built once and never
//! change.
//!
//! This is SP1's `compress_shape.json` mechanism with one extra level. A
//! recursion program's traces are sized by the program alone (its
//! instruction counts), so pinning `program.shape` pads every program of a
//! level to common heights; SP1 pins its normalize and compose programs to
//! its compress shape. Aiur's leaf programs (`AiurRecursiveVerifier` over a
//! 181-chip machine) outgrow SP1's compress row cap, so the leaf level has
//! its own machine configuration ([`crate::pipeline::leaf_params`]) and its
//! own pinned shape; the compose programs that verify leaf proofs are
//! pinned, like everything above them, to a compress shape computed as the
//! fixed point SP1 computes (a compose program of arity `k` over
//! compress-shaped proofs must itself fit the compress shape).
//!
//! The built-in shapes ([`PinnedShapes::builtin`]) are what production
//! uses; they were computed from the largest machine the pipeline supports,
//! and a machine whose leaf programs do not fit them is rejected at setup.
//! `IX_REC_SHAPES=compute` recomputes them for the machine at hand (and
//! `IX_REC_SHAPES_OUT=<file>` saves the result); `IX_REC_SHAPES=<file>`
//! loads a saved set.

use std::{collections::BTreeMap, sync::Arc};

use anyhow::{Context, Result, anyhow};
use serde::{Deserialize, Serialize};
use sp1_hypercube::{
  Machine,
  prover::{DefaultTraceGenerator, ProverSemaphore, TraceGenerator},
};
use sp1_primitives::SP1Field;
use sp1_prover::{CompressAir, shapes::SP1RecursionProofShape};
use sp1_recursion_executor::{RecursionProgram, shape::RecursionShape};

/// The shapes one pipeline is pinned to, with the parameters they were
/// computed under (a pipeline built under different ones rejects them).
#[derive(Clone, Debug, Serialize, Deserialize, PartialEq, Eq)]
pub struct PinnedShapes {
  /// Row counts of the leaf machine's chips every leaf proof has.
  pub leaf: SP1RecursionProofShape,
  /// Row counts every compress-level proof has (SP1's reduce shape role).
  pub compress: SP1RecursionProofShape,
  /// `(log_stacking_height, max_log_row_count)` of the leaf machine.
  pub leaf_params: (u32, usize),
  /// The largest compose fan-in the compress shape was closed under.
  pub arity: usize,
  /// The allowlist tree height the compose programs were built for.
  pub vk_tree_height: usize,
}

impl PinnedShapes {
  const BUILTIN: &str = include_str!("../shapes/pinned.json");

  /// The shapes shipped with the crate.
  pub fn builtin() -> Result<Self> {
    serde_json::from_str::<Option<Self>>(Self::BUILTIN)
      .context("parsing the built-in recursion shapes")?
      .ok_or_else(|| {
        anyhow!(
          "no built-in recursion shapes: compute them with \
           IX_REC_SHAPES=compute IX_REC_SHAPES_OUT=<file> and ship the file \
           as crates/aiur-recursion/shapes/pinned.json"
        )
      })
  }

  pub fn from_file(path: &std::path::Path) -> Result<Self> {
    let bytes = std::fs::read(path)
      .with_context(|| format!("reading {}", path.display()))?;
    serde_json::from_slice(&bytes)
      .with_context(|| format!("parsing {}", path.display()))
  }

  pub fn to_json(&self) -> String {
    serde_json::to_string_pretty(self).expect("shapes serialize")
  }
}

/// Per-chip row counts of a recursion program on `machine`: the heights of
/// its preprocessed traces (a recursion chip's rows are its instructions,
/// so the main traces have the same heights). Generating them costs a
/// fraction of a proving-key setup.
pub fn program_heights(
  runtime: &tokio::runtime::Runtime,
  machine: &Machine<SP1Field, CompressAir<SP1Field>>,
  max_log_row_count: usize,
  program: Arc<RecursionProgram<SP1Field>>,
) -> BTreeMap<String, usize> {
  runtime.block_on(async {
    let generator = DefaultTraceGenerator::new(machine.clone());
    let data = generator
      .generate_preprocessed_traces(
        program,
        max_log_row_count,
        ProverSemaphore::new(1),
      )
      .await;
    data
      .preprocessed_traces
      .into_iter()
      .map(|(name, trace)| (name, trace.num_real_entries()))
      .collect()
  })
}

/// Round heights the way SP1 does (multiples of 32, the public-values chip
/// as is) into a shape.
pub fn shape_from_heights(
  heights: &BTreeMap<String, usize>,
) -> SP1RecursionProofShape {
  let heights = heights
    .iter()
    .map(|(name, &h)| {
      let h = if name == "PublicValues" { h } else { h.next_multiple_of(32) };
      (name.clone(), h)
    })
    .collect();
  SP1RecursionProofShape { shape: RecursionShape::new(heights) }
}

/// The per-chip maximum of two shapes.
pub fn max_shape(
  a: &SP1RecursionProofShape,
  b: &SP1RecursionProofShape,
) -> SP1RecursionProofShape {
  let mut heights: BTreeMap<String, usize> =
    a.shape.clone().into_iter().collect();
  for (name, h) in &b.shape {
    let entry = heights.entry(name.clone()).or_default();
    *entry = (*entry).max(*h);
  }
  SP1RecursionProofShape { shape: RecursionShape::new(heights) }
}

/// Whether a program with these heights can be pinned to `shape`.
pub fn fits(
  shape: &SP1RecursionProofShape,
  heights: &BTreeMap<String, usize>,
) -> Result<(), String> {
  let mut problems = Vec::new();
  for (name, &h) in heights {
    match shape.shape.height_of_name(name) {
      Some(allowed) if h <= allowed => {},
      Some(allowed) => problems.push(format!("{name}: {h} > {allowed}")),
      None => problems.push(format!("{name}: {h} rows, chip not in shape")),
    }
  }
  if problems.is_empty() { Ok(()) } else { Err(problems.join(", ")) }
}

/// Whether every height is under the machine's row cap.
pub fn under_cap(
  heights: &BTreeMap<String, usize>,
  max_log_row_count: usize,
) -> Result<(), String> {
  let cap = 1usize << max_log_row_count;
  let over: Vec<String> = heights
    .iter()
    .filter(|(_, h)| **h > cap)
    .map(|(name, h)| format!("{name}: {h} > 2^{max_log_row_count}"))
    .collect();
  if over.is_empty() { Ok(()) } else { Err(over.join(", ")) }
}

/// The largest height of any chip in `shape`.
pub fn tallest(shape: &SP1RecursionProofShape) -> usize {
  shape.shape.clone().into_iter().map(|(_, h)| h).max().unwrap_or(0)
}
