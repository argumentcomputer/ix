//! Narrow template backend for Aiur's compiled per-function circuits
//! (`docs/aiur-compression-architecture.md`; soundness obligations in
//! `docs/aiur-template-backend.md`). The layout comes from the verified Lean
//! tiling pass ([`v2::lean`]); [`v2::Backend`] builds the narrow circuits and
//! places the witness.

pub mod v2;

use crate::kzg::{KzgConfig, Scalar};
use multi_stark::{
  config::{ProofConfig, Val},
  lookup::{MAX_LOOKUP_GROUP, logup_max_degree, stage2_width},
  system::{CircuitInputs, ProverKey, System, extension_params},
  traits::PrimeField,
};
use serde_json::Value;

/// The system of `inputs`, where `shared[i] = Some(j)` makes circuit `i` read
/// circuit `j`'s fixed matrix. Sharing needs the multi-stark fork's
/// `System::new_shared` (feature `shared-fixed`, built with the fork patched
/// over the pinned multi-stark). Without any shared slot this is the pinned
/// multi-stark's `System::new` (`new_without_preprocessed` unless `retain`),
/// which gives the same system and transcript as the fork does for it.
pub fn system_with_slots<SC: ProofConfig>(
  config: SC,
  inputs: Vec<CircuitInputs<Val<SC>>>,
  shared: &[Option<usize>],
  retain: bool,
) -> Result<(System<SC>, ProverKey<SC>), String> {
  if shared.iter().any(Option::is_some) {
    #[cfg(feature = "shared-fixed")]
    return Ok(System::new_shared(config, inputs, shared, retain));
    #[cfg(not(feature = "shared-fixed"))]
    return Err("shared fixed slots need the `shared-fixed` feature and the multi-stark fork".into());
  }
  Ok(if retain {
    System::new(config, inputs)
  } else {
    System::new_without_preprocessed(config, inputs)
  })
}

/// Committed fixed matrices of `system`: its slots when slots are shared,
/// otherwise one per circuit with a fixed matrix.
pub fn fixed_slots<SC: ProofConfig>(system: &System<SC>) -> usize {
  #[cfg(feature = "shared-fixed")]
  return system.preprocessed_slots();
  #[cfg(not(feature = "shared-fixed"))]
  return system.circuits.iter().filter(|c| c.preprocessed_height != 0).count();
}

pub(super) const CALL: u64 = 1;
pub(super) const ROM: u64 = 2;
/// Chunk `j` of a wide call uses `sub = callable + (j + 1)·CHUNK_STRIDE`; ROM
/// chunk `j` uses `width + j·CHUNK_STRIDE`, so its first chunk keeps the
/// original `(ROM, width)` prefix.
pub(super) const CHUNK_STRIDE: u64 = 1 << 32;

pub(super) fn canonical(value: Scalar) -> Result<u64, String> {
  value.canonical_u64().ok_or_else(|| "non-small constant".to_owned())
}

/// Physical dimensions of one circuit of the narrow system.
#[derive(Clone, Debug, serde::Serialize)]
pub struct CircuitCount {
  pub name: String,
  pub rows: usize,
  pub heights: Vec<usize>,
  pub main: usize,
  pub fixed: usize,
  pub lookups: usize,
  pub lookup_group_size: usize,
  pub stage2: usize,
  pub quotient: usize,
  pub constraint_degree: usize,
  pub evaluations: usize,
  pub main_cells: usize,
  pub committed_cells: usize,
  pub fixed_cells: usize,
}

fn quotient(input: &CircuitInputs<Scalar>, group: usize) -> (usize, usize) {
  let mut probe = input.clone();
  probe.lookup_group_size = group;
  let graph = probe
    .compile_graph(&extension_params::<KzgConfig>())
    .expect("template circuit compiles");
  let degree =
    (graph.max_constraint_degree.max(logup_max_degree(&graph, group))) as usize;
  (degree, (degree.max(2) - 1).next_power_of_two())
}

/// The KZG adapter's budgeted group choice: minimize stage-2 columns plus
/// quotient chunks with quotient degree at most `max(budget, base)`.
fn group_size(input: &CircuitInputs<Scalar>, budget: usize) -> usize {
  let n = input.lookups.len();
  let base = quotient(input, 1).1;
  let budget = budget.max(base);
  let mut best = (stage2_width(n, 1, 1) + base, base, 1);
  for g in 2..=MAX_LOOKUP_GROUP {
    let q = quotient(input, g).1;
    if q <= budget {
      best = best.min((stage2_width(n, g, 1) + q, q, g));
    }
  }
  best.2
}

fn count(
  name: &str,
  input: &CircuitInputs<Scalar>,
  rows: usize,
  heights: Vec<usize>,
) -> CircuitCount {
  let (degree, q) = quotient(input, input.lookup_group_size);
  let stage2 = stage2_width(input.lookups.len(), input.lookup_group_size, 1);
  let fixed = input.preprocessed.as_ref().map_or(0, |m| m.width);
  let shards = heights.len();
  let total: usize = heights.iter().sum();
  CircuitCount {
    name: name.into(),
    rows,
    main: input.main_width,
    fixed,
    lookups: input.lookups.len(),
    lookup_group_size: input.lookup_group_size,
    stage2,
    quotient: q,
    constraint_degree: degree,
    evaluations: shards * (input.main_width + 2 * stage2 + q + fixed),
    main_cells: input.main_width * total,
    committed_cells: (input.main_width + stage2 + q) * total,
    fixed_cells: fixed * total,
    heights,
  }
}

pub(crate) fn decimal(x: Scalar) -> Value {
  let limbs = x.canonical_limbs_le();
  let bytes: Vec<u8> = limbs.iter().flat_map(|l| l.to_le_bytes()).collect();
  Value::String(num_bigint::BigUint::from_bytes_le(&bytes).to_string())
}

pub(crate) fn parse_scalar(v: &Value) -> Result<Scalar, String> {
  let s = v.as_str().ok_or("field element is not a string")?;
  let n: num_bigint::BigUint =
    s.parse().map_err(|e| format!("bad field element {s}: {e}"))?;
  let mut limbs = [0u64; 4];
  for (i, d) in n.to_u64_digits().into_iter().enumerate() {
    *limbs.get_mut(i).ok_or("field element too large")? = d;
  }
  Ok(Scalar::from_limbs_le(limbs))
}

pub(crate) fn usize_of(v: &Value) -> Result<usize, String> {
  v.as_u64()
    .and_then(|n| usize::try_from(n).ok())
    .ok_or_else(|| format!("expected a natural number, got {v}"))
}
