//! Experimental multi-stark adapter for the circuits exported by the verified
//! Aiur compiler.
//!
//! The verifier's program, artifact and fixed tables must come from the trusted
//! compilation, not from the proof supplier. This Rust adapter and multi-stark
//! are outside the Lean proof. The lookup argument alone accepts cyclic memo
//! tables; the exported circuits carry the depth pass (Track A, H1), whose
//! acyclicity argument also needs every verifier to bound a batch's rows by
//! [`MAX_BATCH_ROWS`].
use super::{Polynomial, RangeCounts, Trace, TracePlan};
use crate::shared::Shared;
use crate::{
  Execution,
  field::{FieldBackend, NativeField, PrimeField},
};
use multi_stark::{
  expr::Expr,
  lookup::Lookup,
  p3_adapter::fri_batching::FriBatching,
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::{Matrix, dense::RowMajorMatrix},
  system::{
    CircuitInputs, ProverKey, System, SystemWitness, compute_vk_digest,
  },
  types::{
    CommitmentParameters, ExtVal3, FriParameters, GoldilocksBlake3V6Config, Val,
  },
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
#[cfg(feature = "cuda")]
use rustc_hash::FxHashMap;
use serde::Serialize;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_BACKEND_ID: AtomicU64 = AtomicU64::new(1);

pub mod batch;
#[cfg(feature = "cuda")]
pub mod compiled;
#[cfg(feature = "cuda")]
mod gpu;
mod grouping;
mod lookup_groups;
pub mod planning;
#[cfg(feature = "trace-profile")]
mod profile;
mod rom;
mod statistics;
pub mod streaming;
mod tables;
#[cfg(test)]
mod tests;
pub mod wide;
mod witness;
pub mod zk;
#[cfg(test)]
pub use batch::StageOne;
pub use batch::{
  ShardFeed, StreamPlan, Streamed, VerifyingKey, fri_parameter_bytes,
};
pub use rom::{RomLayout, rom_lanes};
pub use statistics::{CircuitMeasurements, ExecutionStatistics};
pub use witness::ValidatedRecord;
pub use zk::{ZkBackend, ZkProof};

/// Conversion at this concrete proving adapter only. The native configuration
/// writes its existing field values directly into multi-stark's matrices.
pub trait WitnessField: FieldBackend<Word = u64> {
  fn into_stark(value: Self::Element) -> Val;
  /// The elements as Goldilocks words, not necessarily canonical; borrowed
  /// when the representation already is one.
  fn words(values: &[Self::Element]) -> std::borrow::Cow<'_, [u64]> {
    values.iter().map(|&v| Self::into_stark(v).as_canonical_u64()).collect()
  }
}
impl WitnessField for PrimeField {
  fn into_stark(value: u64) -> Val {
    Val::from_u64(value)
  }
  fn words(values: &[u64]) -> std::borrow::Cow<'_, [u64]> {
    std::borrow::Cow::Borrowed(values)
  }
}
impl WitnessField for NativeField<Val> {
  #[inline]
  fn into_stark(value: Val) -> Val {
    value
  }
  fn words(values: &[Val]) -> std::borrow::Cow<'_, [u64]> {
    // SAFETY: `Goldilocks` is `#[repr(transparent)]` over `u64`.
    std::borrow::Cow::Borrowed(unsafe {
      std::slice::from_raw_parts(values.as_ptr().cast::<u64>(), values.len())
    })
  }
}

pub type Proof = multi_stark::prover::Proof<GoldilocksBlake3V6Config>;
pub type BatchProof = multi_stark::batch::BatchProof<GoldilocksBlake3V6Config>;

/// The most weighted logical rows one LogUp batch or single proof may hold,
/// over every shard and active circuit (padded heights, weighting `K`-lane
/// vectorized ROM circuits — both segmented and unsegmented — by `K`, which
/// only over-counts). The depth pass's acyclicity argument needs
/// `MAX_BATCH_ROWS · 2^24 < p`: a memo cycle among `L` rows lowers depth words
/// by `1 + gap ∈ [1, 2^24]` per row and must sum to a multiple of `p`, so it
/// needs `L · 2^24 ≥ p` (`Depth.checkMemo_sound`,
/// `Depth.goldilocks_characteristic`). Both batch and single-proof shape
/// checks enforce this weighted bound, as do the in-circuit verifiers.
pub const MAX_BATCH_ROWS: u64 = 1 << 39;

// Separate message namespaces; callable/type IDs fix the shape within each.
const CALL: u64 = 1;
const ROM: u64 = 2;
pub const MEMSEG: u64 = 16;

/// The FRI parameters that vary. This adapter and the recursive verifier fix
/// the rest: binary folding, a constant final polynomial and root Merkle caps
/// (which also cover height-one circuits). Every field is written into the
/// verifying key and seeds the transcript, so a proof made under other
/// parameters does not verify against a key built with these. Building a
/// backend rejects parameters below the security floor
/// ([`stark_key::security`]); `docs/stark-parameters.md` gives the levels.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub struct Parameters {
  pub log_blowup: usize,
  pub num_queries: usize,
  /// Proof of work before each FRI folding challenge.
  pub commit_proof_of_work_bits: usize,
  /// Proof of work before the FRI query indices are sampled.
  pub query_proof_of_work_bits: usize,
}
impl Parameters {
  /// Protocol v6 (Fp^3) default parameters: blowup 4, 128 queries and 20
  /// query proof-of-work bits (142.24 bits finite-m Johnson with +14.24 bits
  /// headroom, 106.78 bits provable UD, 276 bits conjectured). The Lean mirror
  /// is `Aiur.defaultCommitmentParameters` and `Aiur.defaultFriParameters` in
  /// `Ix/Aiur/Parameters.lean`, checked by the test `lean_mirror_matches`.
  pub const DEFAULT: Self = Self {
    log_blowup: 2,
    num_queries: 128,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 20,
  };

  pub const fn commitment(self) -> CommitmentParameters {
    CommitmentParameters { log_blowup: self.log_blowup, cap_height: 0 }
  }
  pub const fn fri(self) -> FriParameters {
    FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: self.num_queries,
      commit_proof_of_work_bits: self.commit_proof_of_work_bits,
      query_proof_of_work_bits: self.query_proof_of_work_bits,
    }
  }
  /// `log_blowup · num_queries + query_proof_of_work_bits`.
  pub const fn conjectured_bits(self) -> usize {
    stark_key::security::conjectured_bits(&self.commitment(), &self.fri())
  }
  /// The security floor ([`stark_key::security::check`]).
  pub fn check(self) -> Result<(), String> {
    stark_key::security::check(&self.commitment(), &self.fri())
  }
}
impl Default for Parameters {
  fn default() -> Self {
    Self::DEFAULT
  }
}

#[derive(Clone, Debug, Serialize)]
pub struct CircuitStatistics {
  pub name: String,
  pub stage1_width: usize,
  pub stage2_width: usize,
  pub preprocessed_width: usize,
  pub preprocessed_height: usize,
  pub lookups: usize,
  pub lookup_group_size: usize,
  pub quotient_degree: usize,
}

/// Set up once, then prove many records. Only this adapter selects Goldilocks;
/// the compiler, circuit export and ordinary execution remain field generic.
pub struct Backend<'p, 'a, B: WitnessField = PrimeField> {
  id: u64,
  plan: Shared<'p, TracePlan<'a, B>>,
  /// Identifies the records prepared by this backend, whose placements and
  /// device allocations are valid only here.
  preparation_identity: std::sync::Arc<()>,
  system: System<GoldilocksBlake3V6Config>,
  key: ProverKey<GoldilocksBlake3V6Config>,
  names: Vec<String>,
  tables: Vec<tables::FixedTable>,
  rom: rom::Rom,
  lookup_plans: Vec<witness::LookupPlan>,
  member_lookup_plans: Vec<witness::MemberLookupPlan>,
  circuit_chips: Vec<Vec<usize>>,
  members: Vec<Vec<usize>>,
  placements: Vec<grouping::Placement>,
  parameters: Parameters,
  segmented_memory: bool,
  gpu_lookup_only: bool,
  committed: bool,
  /// The device a CUDA backend proves on, and its device population plans
  /// when `AIUR_GPU_TRACE=generated`.
  #[cfg(feature = "cuda")]
  device: i32,
  #[cfg(feature = "cuda")]
  device_plans: Option<gpu::DevicePlans>,
}

/// Whether lookup witnesses are shape-only, leaving the CUDA prover to
/// derive every lookup message from the committed trace. This is the CUDA
/// default: multi-stark rebuilds the values from the commitment on the rare
/// paths that need them on the host, so it changes no proof byte. Set
/// `AIUR_TRACE_ONLY_LOOKUPS=0` to build host lookup buffers anyway; CPU
/// builds always build them and reject `AIUR_TRACE_ONLY_LOOKUPS=1`.
fn device_lookups() -> Result<bool, String> {
  match std::env::var("AIUR_TRACE_ONLY_LOOKUPS") {
    Ok(value) if value == "1" => Ok(true),
    Ok(value) if value == "0" => Ok(false),
    Ok(value) if value.is_empty() => Ok(cfg!(feature = "cuda")),
    Ok(value) => {
      Err(format!("AIUR_TRACE_ONLY_LOOKUPS must be 0 or 1, not {value:?}"))
    },
    Err(_) => Ok(cfg!(feature = "cuda")),
  }
}

fn constant(x: u64) -> Expr<Val> {
  Expr::constant(Val::from_u64(x))
}
fn main_var(i: usize) -> Expr<Val> {
  Expr::main(u32::try_from(i).expect("checked column width"))
}

fn lower(p: &Polynomial) -> Expr<Val> {
  match p {
    Polynomial::Const(x) => constant(*x),
    Polynomial::Var(i) => main_var(*i),
    Polynomial::Add(p) => lower(&p[0]) + lower(&p[1]),
    Polynomial::Sub(p) => lower(&p[0]) - lower(&p[1]),
    Polynomial::Mul(p) => lower(&p[0]) * lower(&p[1]),
  }
}

fn degree(e: &Expr<Val>) -> usize {
  match e {
    Expr::Const(_) | Expr::Public(_) | Expr::IsTransition => 0,
    Expr::Var(_) | Expr::IsFirstRow | Expr::IsLastRow => 1,
    Expr::Add(a, b) | Expr::Sub(a, b) => degree(a).max(degree(b)),
    Expr::Mul(a, b) => degree(a) + degree(b),
    Expr::Neg(a) => degree(a),
  }
}

/// Match fixed domains, bound total unit lookup consumers below the
/// characteristic and total rows by [`MAX_BATCH_ROWS`]. Root caps cover
/// every active matrix, including height 1.
fn check_system_shape(
  system: &System<GoldilocksBlake3V6Config>,
  parameters: Parameters,
  active: &[bool],
  degrees: &[u8],
) -> Result<(), String> {
  if active.len() != system.circuits.len() || !active.contains(&true) {
    return Err("invalid circuit activation".into());
  }
  let mut degrees = degrees.iter();
  let mut budget = 1u64; // one public root
  let mut rows = 0u64;
  for (circuit, &on) in system.circuits.iter().zip(active) {
    if !on {
      if circuit.preprocessed_height != 0 {
        return Err("inactive fixed table".into());
      }
      continue;
    }
    let log = *degrees.next().ok_or("missing trace height")?;
    // Goldilocks has 2-adicity 32. Include the commitment blowup.
    if usize::from(log) + parameters.log_blowup > 32 {
      return Err("trace domain exceeds Goldilocks capacity".into());
    }
    let height = 1u64 << log;
    if circuit.preprocessed_height != 0
      && circuit.preprocessed_height as u64 != height
    {
      return Err("fixed table height mismatch".into());
    }
    let weight = batch::circuit_row_weight(circuit);
    rows = height
      .checked_mul(weight)
      .and_then(|w| rows.checked_add(w))
      .filter(|&r| r <= MAX_BATCH_ROWS)
      .ok_or("trace rows exceed the batch row bound (2^39)")?;
    budget = height
      .checked_mul(circuit.num_lookups.max(1) as u64)
      .and_then(|n| budget.checked_add(n))
      .filter(|&n| n < Val::ORDER_U64)
      .ok_or("lookup count reaches field characteristic")?;
  }
  if degrees.next().is_some() {
    return Err("extra trace heights".into());
  }
  Ok(())
}

/// Reject constraint degrees the blowup cannot hold (before `System::new`'s
/// assertion), build the system, then group lookup messages wherever the
/// circuit's quotient degree already suffices. Grouping reduces stage 2
/// without making its FFTs or the quotient FFT larger, and is decided on the
/// compiled (constant-folded) degrees.
fn build_system(
  inputs: Vec<CircuitInputs<Val>>,
  names: &[String],
  parameters: Parameters,
  device: Option<i32>,
) -> Result<
  (System<GoldilocksBlake3V6Config>, ProverKey<GoldilocksBlake3V6Config>),
  String,
> {
  let max_degree = (1 << parameters.log_blowup) + 1;
  for (input, name) in inputs.iter().zip(names) {
    let user_degree = input.constraints.iter().map(degree).max().unwrap_or(0);
    let lookup_degree = input
      .lookups
      .iter()
      .map(|l| {
        (l.args.iter().map(degree).max().unwrap_or(0) + 1)
          .max(degree(&l.multiplicity))
      })
      .max()
      .unwrap_or(1);
    if user_degree.max(lookup_degree) > max_degree {
      return Err(format!(
        "{name}: increase log_blowup for constraint degree {}",
        user_degree.max(lookup_degree)
      ));
    }
  }
  let config = GoldilocksBlake3V6Config::with_device(
    parameters.commitment(),
    parameters.fri(),
    FriBatching::Tensor,
    device,
  );
  let (mut system, key) = System::new(config, inputs);
  // Tune lookup group sizes against the FFT cost model within the blowup
  // budget before exposing the system, compiling lookup plans, or exporting
  // keys.
  let blowup = 1usize << parameters.log_blowup;
  let ext_degree =
    multi_stark::system::extension_params::<GoldilocksBlake3V6Config>().degree;
  for circuit in &mut system.circuits {
    lookup_groups::retune(circuit, blowup, ext_degree);
  }
  // Retuning lookup_group_size updates stage_2_width/constraint_count/max_constraint_degree
  // on circuits, so recompute vk_digest to match the finalized circuits.
  system.vk_digest = compute_vk_digest::<Val, ExtVal3>(&system.circuits);
  Ok((system, key))
}

impl<'p, 'a, B: WitnessField> Backend<'p, 'a, B> {
  pub fn new(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
  ) -> Result<Self, String> {
    Self::new_with_rom_layout(plan, parameters, RomLayout::Vectorized)
  }

  /// Standalone (non-segmented) backend placed on an optional CUDA device.
  pub fn new_on_device(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    device: Option<i32>,
  ) -> Result<Self, String> {
    Self::build(plan, parameters, false, RomLayout::Vectorized, device, true)
  }

  pub fn new_with_rom_layout(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    rom_layout: RomLayout,
  ) -> Result<Self, String> {
    Self::with_memory_policy(plan, parameters, false, rom_layout)
  }

  /// Batch proofs close contiguous memory ranges through authenticated
  /// boundary messages. A standalone proof uses the original first-row rule.
  pub fn for_batch(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
  ) -> Result<Self, String> {
    Self::for_batch_with_rom_layout(plan, parameters, RomLayout::Vectorized)
  }

  pub fn for_batch_with_rom_layout(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    rom_layout: RomLayout,
  ) -> Result<Self, String> {
    Self::with_memory_policy(plan, parameters, true, rom_layout)
  }

  /// Reconstruct the trusted batch system for verification or key export.
  /// Prover-only lookup settings must not affect these operations. Use the CPU
  /// host binary when verification must not initialize the CUDA backend.
  pub fn for_batch_verification(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
  ) -> Result<Self, String> {
    Self::for_batch_verification_with_rom_layout(
      plan,
      parameters,
      RomLayout::Vectorized,
    )
  }

  pub fn for_batch_verification_with_rom_layout(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    rom_layout: RomLayout,
  ) -> Result<Self, String> {
    Self::assemble(plan, parameters, true, rom_layout, None, false, true, true)
  }

  /// Build circuit shapes, widths and lookup groupings without committing
  /// preprocessed fixed tables, for execution statistics and shape inspection.
  /// Prover-only lookup settings are ignored; proving, verification, witness
  /// generation and key export fail closed on the returned backend.
  pub fn for_statistics(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
  ) -> Result<Self, String> {
    Self::assemble(
      plan,
      parameters,
      true,
      RomLayout::Vectorized,
      None,
      false,
      true,
      false,
    )
  }

  /// Like [`Self::for_statistics`], but honors prover lookup and device
  /// placement policy so resource planning matches [`Self::for_batch_on_device`]
  /// without committing preprocessed fixed tables.
  pub fn for_planning(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    device: Option<i32>,
  ) -> Result<Self, String> {
    let gpu_lookup_only = device_lookups()?;
    Self::assemble(
      plan,
      parameters,
      true,
      RomLayout::Vectorized,
      device,
      gpu_lookup_only,
      true,
      false,
    )
  }

  /// Explicit CUDA placement. CPU builds reject a requested device instead of
  /// silently running a different backend. Device placement does not change keys.
  pub fn for_batch_on_device(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    device: Option<i32>,
  ) -> Result<Self, String> {
    Self::for_batch_on_device_with_rom_layout(
      plan,
      parameters,
      RomLayout::Vectorized,
      device,
    )
  }

  /// [`Self::for_batch_on_device`] with an explicit ROM row layout (e.g.
  /// [`RomLayout::Scalar`] for Lean-exported wide stages whose `romCircuit`
  /// stores one entry per row).
  pub fn for_batch_on_device_with_rom_layout(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    rom_layout: RomLayout,
    device: Option<i32>,
  ) -> Result<Self, String> {
    Self::build(plan, parameters, true, rom_layout, device, true)
  }

  /// [`Self::new`] without the security floor, for tests whose toy parameters
  /// keep proving fast. A verifier must never trust a proof from such a
  /// backend.
  #[doc(hidden)]
  pub fn new_below_floor(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
  ) -> Result<Self, String> {
    Self::new_below_floor_with_rom_layout(
      plan,
      parameters,
      RomLayout::Vectorized,
    )
  }

  /// [`Self::new_with_rom_layout`] without the security floor, for tests.
  #[doc(hidden)]
  pub fn new_below_floor_with_rom_layout(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    rom_layout: RomLayout,
  ) -> Result<Self, String> {
    Self::build(plan, parameters, false, rom_layout, None, false)
  }

  /// [`Self::for_batch`] without the security floor, for tests whose toy
  /// parameters keep recursive verifier circuits small. A verifier must never
  /// trust a key or proof from such a backend.
  #[doc(hidden)]
  pub fn for_batch_below_floor(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
  ) -> Result<Self, String> {
    Self::for_batch_below_floor_with_rom_layout(
      plan,
      parameters,
      RomLayout::Vectorized,
    )
  }

  #[doc(hidden)]
  pub fn for_batch_below_floor_with_rom_layout(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    rom_layout: RomLayout,
  ) -> Result<Self, String> {
    Self::build(plan, parameters, true, rom_layout, None, false)
  }

  fn with_memory_policy(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    segmented_memory: bool,
    rom_layout: RomLayout,
  ) -> Result<Self, String> {
    Self::build(plan, parameters, segmented_memory, rom_layout, None, true)
  }

  fn build(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    segmented_memory: bool,
    rom_layout: RomLayout,
    device: Option<i32>,
    floor: bool,
  ) -> Result<Self, String> {
    let gpu_lookup_only = device_lookups()?;
    #[allow(unused_mut)]
    let mut backend = Self::assemble(
      plan,
      parameters,
      segmented_memory,
      rom_layout,
      device,
      gpu_lookup_only,
      floor,
      true,
    )?;
    // Only proving backends populate traces; verification ignores this.
    #[cfg(feature = "cuda")]
    {
      backend.device_plans = gpu::DevicePlans::from_env(&backend)?;
      if let Some(plans) = &backend.device_plans {
        eprintln!("[aiur/gpu] {}", plans.summary(&backend));
      }
    }
    Ok(backend)
  }

  #[cfg(all(test, feature = "cuda"))]
  fn build_with_lookup_policy(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    segmented_memory: bool,
    device: Option<i32>,
    gpu_lookup_only: bool,
  ) -> Result<Self, String> {
    Self::assemble(
      plan,
      parameters,
      segmented_memory,
      RomLayout::Vectorized,
      device,
      gpu_lookup_only,
      true,
      true,
    )
  }
  fn assemble(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    segmented_memory: bool,
    rom_layout: RomLayout,
    device: Option<i32>,
    gpu_lookup_only: bool,
    floor: bool,
    commit: bool,
  ) -> Result<Self, String> {
    if floor {
      parameters.check()?;
    } else if !stark_key::security::LOG_BLOWUP_RANGE
      .contains(&parameters.log_blowup)
      || parameters.num_queries == 0
    {
      return Err(
        "expected log_blowup in 1..=4 and positive num_queries".into(),
      );
    }
    if gpu_lookup_only && !cfg!(feature = "cuda") {
      return Err("AIUR_TRACE_ONLY_LOOKUPS=1 requires a CUDA build".into());
    }
    if device.is_some_and(|d| d < 0) {
      return Err("negative CUDA device".into());
    }
    #[cfg(not(feature = "cuda"))]
    if device.is_some() {
      return Err(
        "GPU device requested from a CPU build; build with the cuda feature"
          .into(),
      );
    }
    let plan: Shared<'p, TracePlan<'a, B>> = plan.into();
    if plan.program.field.modulus() != Val::ORDER_U64 {
      return Err("multi-stark adapter requires the Goldilocks field".into());
    }
    let rom = rom::Rom::new(&plan, rom_layout);
    let mut inputs = vec![];
    let mut names = vec![];
    let placements = grouping::build(&plan, &rom, &mut inputs, &mut names)?;
    let function_circuits = inputs.len();
    let tables = tables::fixed_tables(
      &plan,
      &mut inputs,
      &mut names,
      parameters.log_blowup,
      commit,
      0,
      false,
    )?;
    rom.append_circuits(&mut inputs, &mut names, segmented_memory)?;
    let (system, key) = if commit {
      build_system(inputs, &names, parameters, device)?
    } else {
      let config = GoldilocksBlake3V6Config::with_device(
        parameters.commitment(),
        parameters.fri(),
        FriBatching::Tensor,
        device,
      );
      let (mut system, key) = Self::compile_system_without_commit(
        config,
        inputs,
        function_circuits..function_circuits + tables.len(),
        &tables,
      )?;
      let blowup = 1usize << parameters.log_blowup;
      let ext_degree =
        multi_stark::system::extension_params::<GoldilocksBlake3V6Config>()
          .degree;
      for circuit in &mut system.circuits {
        lookup_groups::retune(circuit, blowup, ext_degree);
      }
      system.vk_digest = compute_vk_digest::<Val, ExtVal3>(&system.circuits);
      (system, key)
    };
    let lookup_plans = if commit {
      system
        .circuits
        .iter()
        .map(|circuit| witness::LookupPlan::compile(&circuit.graph))
        .collect::<Result<_, _>>()?
    } else {
      vec![]
    };
    let member_lookup_plans = if commit {
      witness::compile_member_lookup_plans(&placements, &system.circuits)?
    } else {
      vec![]
    };
    let mut circuit_chips = vec![vec![]; function_circuits];
    for (chip, placement) in placements.iter().enumerate() {
      circuit_chips[placement.circuit].push(chip);
    }
    let mut members = vec![vec![]; function_circuits];
    for (function, &chip) in plan.members.iter().enumerate() {
      members[placements[chip].circuit].push(function);
    }
    let backend = Self {
      id: NEXT_BACKEND_ID.fetch_add(1, Ordering::Relaxed),
      plan,
      preparation_identity: std::sync::Arc::new(()),
      system,
      key,
      names,
      tables,
      rom,
      lookup_plans,
      member_lookup_plans,
      circuit_chips,
      members,
      placements,
      parameters,
      segmented_memory,
      gpu_lookup_only,
      committed: commit,
      #[cfg(feature = "cuda")]
      device: device.unwrap_or_else(|| {
        std::env::var("MULTI_STARK_CUDA_DEVICE")
          .ok()
          .and_then(|v| v.parse().ok())
          .unwrap_or(0)
      }),
      #[cfg(feature = "cuda")]
      device_plans: None,
    };
    Ok(backend)
  }

  /// Compile constraint graphs and derive circuit metadata identically to
  /// [`System::new`], skipping preprocessed fixed-table PCS commitment.
  fn compile_system_without_commit(
    config: GoldilocksBlake3V6Config,
    inputs: Vec<CircuitInputs<Val>>,
    table_range: std::ops::Range<usize>,
    tables: &[tables::FixedTable],
  ) -> Result<
    (System<GoldilocksBlake3V6Config>, ProverKey<GoldilocksBlake3V6Config>),
    String,
  > {
    use multi_stark::{
      config::ProofConfig,
      lookup::{
        MAX_LOOKUP_GROUP, logup_constraint_count, logup_max_degree,
        num_publics, stage2_width,
      },
      system::{Circuit, extension_params},
    };
    let params = extension_params::<GoldilocksBlake3V6Config>();
    let d = params.degree;
    let mut circuits = Vec::with_capacity(inputs.len());
    let mut preprocessed_indices = Vec::with_capacity(inputs.len());
    for (i, mut input) in inputs.into_iter().enumerate() {
      let num_lookups = input.lookups.len();
      let group_size = input.lookup_group_size.max(1);
      if group_size > MAX_LOOKUP_GROUP {
        return Err(format!(
          "circuit {i}: lookup_group_size {group_size} exceeds MAX_LOOKUP_GROUP"
        ));
      }
      input.lookup_group_size = group_size;
      let (preprocessed_width, preprocessed_height) =
        if table_range.contains(&i) {
          let table = &tables[i - table_range.start];
          (table.preprocessed_width, table.height)
        } else {
          (
            input.preprocessed.as_ref().map_or(0, Matrix::width),
            input.preprocessed.as_ref().map_or(0, Matrix::height),
          )
        };
      let s2_width = stage2_width(num_lookups, group_size, d);
      let n_publics = num_publics(d);
      let graph = input.compile_graph(&params).map_err(|e| {
        format!("circuit {i}: constraint compilation failed: {e:?}")
      })?;
      let constraint_count =
        graph.zeros.len() + logup_constraint_count(num_lookups, group_size, d);
      let max_constraint_degree =
        (graph.max_constraint_degree.max(logup_max_degree(&graph, group_size)))
          as usize;
      let circuit = Circuit {
        graph,
        main_width: input.main_width,
        preprocessed: None,
        preprocessed_width,
        preprocessed_height,
        num_lookups,
        stage_2_width: s2_width,
        num_publics: n_publics,
        lookup_group_size: group_size,
        constraint_count,
        max_constraint_degree,
      };
      if circuit.quotient_degree() > config.max_quotient_degree() {
        return Err(format!(
          "circuit {i}: constraint degree {} needs quotient degree {}, but PCS supports {}",
          circuit.max_constraint_degree(),
          circuit.quotient_degree(),
          config.max_quotient_degree(),
        ));
      }
      preprocessed_indices.push(None);
      circuits.push(circuit);
    }
    let vk_digest = compute_vk_digest::<Val, ExtVal3>(&circuits);
    let system = System {
      config,
      circuits,
      preprocessed_commit: None,
      preprocessed_indices,
      vk_digest,
    };
    Ok((system, ProverKey { preprocessed_data: None }))
  }

  fn require_committed(&self) -> Result<(), String> {
    if !self.committed {
      return Err(
        "statistics/planning backend has no preprocessed commitment".into(),
      );
    }
    Ok(())
  }

  pub const fn parameters(&self) -> Parameters {
    self.parameters
  }

  pub const fn system(&self) -> &System<GoldilocksBlake3V6Config> {
    &self.system
  }

  pub const fn rom_layout(&self) -> RomLayout {
    self.rom.layout
  }

  pub fn statistics(&self) -> Vec<CircuitStatistics> {
    self
      .system
      .circuits
      .iter()
      .zip(&self.names)
      .map(|(c, name)| CircuitStatistics {
        name: name.clone(),
        stage1_width: c.main_width,
        stage2_width: c.stage_2_width,
        preprocessed_width: c.preprocessed_width,
        preprocessed_height: c.preprocessed_height,
        lookups: c.num_lookups,
        lookup_group_size: c.lookup_group_size,
        quotient_degree: c.quotient_degree(),
      })
      .collect()
  }

  /// The public claim `[CALL, entry, args…, output…]`. A recursive entry's
  /// claim also carries a depth word, which `args` must end with
  /// ([`TracePlan::public_args`] gives the recorded one); the depth pass's
  /// soundness holds for every value.
  pub fn claim(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
  ) -> Result<Vec<Val>, String> {
    let id = self.plan.program.entry(entry)?.function;
    let chip = &self.plan.artifact.chips[self.plan.members[id]];
    let (inputs, depth) = self.plan.entry_args(id, args);
    self.plan.program.inputs[id].validate(inputs, self.plan.program.field)?;
    self.plan.program.outputs[id].validate(output, self.plan.program.field)?;
    if chip.depth.column.is_some() && depth.is_none() {
      return Err(format!(
        "{entry} is recursive: its public claim needs a depth word after its arguments"
      ));
    }
    Ok(
      [CALL, self.plan.callables[&chip.name] as u64]
        .into_iter()
        .map(Val::from_u64)
        .chain(inputs.iter().copied().map(B::into_stark))
        .chain(depth.map(B::into_stark))
        .chain(output.iter().copied().map(B::into_stark))
        .collect(),
    )
  }

  /// Convert populated function rows, copy fixed-table/ROM counts from the
  /// execution record, then evaluate the lookup prefix. Zero padding emits
  /// no demands, so the recorded counts need no adjustment.
  /// This validates shapes and recorded counts. Use TracePlan::check
  /// for row diagnostics; the proof enforces equations and lookup balance.
  pub fn witness(
    &self,
    record: &Execution<B>,
    trace: &Trace<B::Element>,
  ) -> Result<SystemWitness<Val>, String> {
    self.require_committed()?;
    self.plan.validate_record(record)?;
    if trace.matrices.len() != self.plan.artifact.chips.len() {
      return Err("trace matrix count mismatch".into());
    }
    let table_counts = self.auxiliary_counts(record, &trace.ranges)?;
    let traces = self.convert_traces(record, trace, &table_counts)?;
    let (active, degrees) = self.trace_shape(&traces)?;
    self.check_shape(&active, &degrees)?;
    Ok(self.witness_from_main(traces))
  }

  #[cfg(test)]
  /// Build a stage-one witness with empty lookup buffers when only the
  /// stage-one commitment header is needed (for example, round one of a
  /// regenerated batch where `Stage1` is dropped immediately after hashing its
  /// header).
  fn header_only_witness_from_main(
    &self,
    traces: Vec<RowMajorMatrix<Val>>,
  ) -> SystemWitness<Val> {
    let lookups = (0..traces.len())
      .map(|_| multi_stark::lookup::LookupValues::builder(0, &[]).finish())
      .collect();
    SystemWitness { traces, lookups }
  }

  /// CUDA's graph evaluator derives lookup messages from committed rows.
  /// Shape-only buffers deliberately fail closed if a CPU fallback tries to
  /// consume them. Full host buffers remain the default for fallback support.
  fn witness_from_main(
    &self,
    traces: Vec<RowMajorMatrix<Val>>,
  ) -> SystemWitness<Val> {
    #[cfg(feature = "trace-profile")]
    let _profile = profile::Span::new(
      "shard_lookups",
      traces.iter().map(|t| t.values.len()).sum(),
    );
    if self.gpu_lookup_only {
      let lookups = traces
        .iter()
        .zip(&self.system.circuits)
        .map(|(trace, circuit)| {
          let widths: Vec<_> =
            circuit.graph.lookups.iter().map(|l| l.args.len()).collect();
          multi_stark::lookup::LookupValues::shape_only(trace.height(), &widths)
        })
        .collect();
      SystemWitness { traces, lookups }
    } else {
      // This adapter, which the Lean proofs do not cover, accepts only
      // row-local lookup expressions.
      // Reuse its compiled writer after slicing, just as in fused generation,
      // instead of serially interpreting the full graph for every padded row.
      #[cfg(feature = "parallel")]
      let lookups = traces
        .par_iter()
        .enumerate()
        .map(|(ci, trace)| self.auxiliary_lookups(ci, trace))
        .collect();
      #[cfg(not(feature = "parallel"))]
      let lookups = traces
        .iter()
        .enumerate()
        .map(|(ci, trace)| self.auxiliary_lookups(ci, trace))
        .collect();
      SystemWitness { traces, lookups }
    }
  }

  /// Fixed-table counts: execution's uses of each map, plus population's
  /// uses of the depth range tables (`ranges`), which execution never calls.
  fn auxiliary_counts(
    &self,
    record: &Execution<B>,
    ranges: &RangeCounts,
  ) -> Result<Vec<Vec<u64>>, String> {
    let program = &self.plan.program.program;
    let counts = |mi: usize| {
      let map = record.queries.tables[program.functions.len() + mi]
        .static_map
        .as_ref()
        .ok_or("missing fixed-table record")?;
      if map.counts.iter().any(|&count| count >= Val::ORDER_U64) {
        return Err("table count reaches field characteristic".into());
      }
      Ok::<_, String>(map.counts.to_vec())
    };
    #[cfg(feature = "parallel")]
    let table_counts = (0..program.maps.len())
      .into_par_iter()
      .map(counts)
      .collect::<Result<_, _>>()?;
    #[cfg(not(feature = "parallel"))]
    let table_counts =
      (0..program.maps.len()).map(counts).collect::<Result<_, _>>()?;
    let mut table_counts: Vec<Vec<u64>> = table_counts;
    self.add_range_counts(&mut table_counts, ranges)?;
    if record.memory.iter().any(|entry| entry.multiplicity >= Val::ORDER_U64) {
      return Err("ROM count reaches field characteristic".into());
    }
    Ok(table_counts)
  }

  /// Adds the depth range tables' uses `ranges` to fixed-table counts
  /// `table_counts`, as [`Self::auxiliary_counts`] lays them out.
  fn add_range_counts(
    &self,
    table_counts: &mut [Vec<u64>],
    ranges: &RangeCounts,
  ) -> Result<(), String> {
    let functions = self.plan.program.program.functions.len();
    for (table, range) in self.plan.depth.tables.iter().enumerate() {
      let uses = ranges.table(table);
      let counts = &mut table_counts[range.map - functions];
      if uses.len() > counts.len() {
        return Err("depth range counts exceed their table".into());
      }
      for (count, &n) in counts.iter_mut().zip(uses) {
        *count = count
          .checked_add(n)
          .filter(|&c| c < Val::ORDER_U64)
          .ok_or("table count reaches field characteristic")?;
      }
    }
    Ok(())
  }

  fn convert_traces(
    &self,
    record: &Execution<B>,
    trace: &Trace<B::Element>,
    table_counts: &[Vec<u64>],
  ) -> Result<Vec<RowMajorMatrix<Val>>, String> {
    let mut heights = vec![0usize; self.members.len()];
    for (ci, matrix) in trace.matrices.iter().enumerate() {
      let placement = &self.placements[ci];
      let n = &mut heights[placement.circuit];
      let height =
        if placement.grouped { matrix.unpadded_height } else { matrix.height };
      *n = n.checked_add(height).ok_or("group height overflow")?;
    }
    let mut traces = heights
      .iter()
      .enumerate()
      .map(|(ci, &height)| {
        let padded = if height == 0 {
          0
        } else {
          height.checked_next_power_of_two().ok_or("group height overflow")?
        };
        let width = self.system.circuits[ci].main_width;
        Ok(RowMajorMatrix::new(
          Val::zero_vec(
            padded.checked_mul(width).ok_or("group trace size overflow")?,
          ),
          width,
        ))
      })
      .collect::<Result<Vec<_>, String>>()?;
    let mut cursors = vec![0usize; self.members.len()];
    for (ci, (chip, matrix)) in
      self.plan.artifact.chips.iter().zip(&trace.matrices).enumerate()
    {
      if matrix.chip != chip.name
        || matrix.width != chip.width
        || matrix.unpadded_height > matrix.height
        || matrix.height.checked_mul(matrix.width) != Some(matrix.values.len())
        || matrix.multiplicities.len() != matrix.height
        || (matrix.height != 0 && !matrix.height.is_power_of_two())
        || matrix.values.iter().any(|&x| !self.plan.program.field.valid(x))
        || matrix.multiplicities.iter().any(|&x| x >= Val::ORDER_U64)
      {
        return Err(format!("{}: malformed STARK trace", chip.name));
      }
      let placement = &self.placements[ci];
      let output = &mut traces[placement.circuit];
      let width = output.width;
      for r in 0..matrix.height {
        let row = matrix.row(r);
        let active = row[chip.activation];
        if active != self.plan.program.field.zero()
          && active != self.plan.program.field.one()
        {
          return Err("non-boolean row activation".into());
        }
        if active == self.plan.program.field.zero()
          && matrix.multiplicities[r] != 0
        {
          return Err("inactive row provides a claim".into());
        }
        if r >= matrix.unpadded_height {
          if row.iter().any(|&x| x != self.plan.program.field.zero())
            || matrix.multiplicities[r] != 0
          {
            return Err("nonzero trace padding".into());
          }
          continue;
        }
        if active != self.plan.program.field.one() {
          return Err("inactive real row".into());
        }
        let cursor = &mut cursors[placement.circuit];
        let dest = &mut output.values[*cursor * width..(*cursor + 1) * width];
        for (&column, &value) in placement.columns.iter().zip(row) {
          dest[column] = B::into_stark(value);
        }
        placement.finish(dest, matrix.multiplicities[r]);
        *cursor += 1;
      }
    }
    for table in &self.tables {
      traces.push(table.witness(table_counts));
    }
    for i in 0..self.rom.circuit_count() {
      traces.push(self.rom.witness(record, i, None)?);
    }
    Ok(traces)
  }

  fn trace_shape(
    &self,
    traces: &[RowMajorMatrix<Val>],
  ) -> Result<(Vec<bool>, Vec<u8>), String> {
    self.trace_shape_with(traces, &[])
  }

  /// `device` gives the heights of circuits populated on the GPU, whose host
  /// matrices are empty placeholders.
  fn trace_shape_with(
    &self,
    traces: &[RowMajorMatrix<Val>],
    device: &[Option<usize>],
  ) -> Result<(Vec<bool>, Vec<u8>), String> {
    if traces.len() != self.system.circuits.len() {
      return Err("wrong circuit count".into());
    }
    let mut active = vec![];
    let mut degrees = vec![];
    for (ci, (trace, circuit)) in
      traces.iter().zip(&self.system.circuits).enumerate()
    {
      let height =
        device.get(ci).copied().flatten().unwrap_or_else(|| trace.height());
      if trace.width != circuit.main_width
        || !trace.values.len().is_multiple_of(trace.width)
        || (height != 0 && !height.is_power_of_two())
      {
        return Err("invalid main trace shape".into());
      }
      active.push(height != 0);
      if height != 0 {
        degrees.push(
          u8::try_from(height.ilog2())
            .ok()
            .ok_or("trace height log overflow")?,
        );
      }
    }
    Ok((active, degrees))
  }

  /// [`check_system_shape`] of this backend's system.
  fn check_shape(&self, active: &[bool], degrees: &[u8]) -> Result<(), String> {
    check_system_shape(&self.system, self.parameters, active, degrees)
  }

  /// Prove an already prepared witness. A malformed witness may produce an
  /// invalid proof; verification, not the witness generator, is authoritative.
  pub fn prove(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    witness: SystemWitness<Val>,
  ) -> Result<Proof, String> {
    self.require_committed()?;
    if self.segmented_memory {
      return Err("segmented memory requires a batch proof".into());
    }
    let claim = self.claim(entry, args, output)?;
    let (active, degrees) = self.trace_shape(&witness.traces)?;
    self.check_shape(&active, &degrees)?;
    if witness.lookups.len() != self.system.circuits.len() {
      return Err("wrong lookup witness count".into());
    }
    Ok(self.system.prove(&self.key, &claim, witness))
  }

  /// Prove directly from stage-one main traces, evaluating lookup messages
  /// lazily per circuit instead of materializing all host lookup buffers upfront.
  pub fn prove_streaming(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    traces: Vec<RowMajorMatrix<Val>>,
  ) -> Result<Proof, String> {
    self.require_committed()?;
    if self.segmented_memory {
      return Err("segmented memory requires a batch proof".into());
    }
    let claim = self.claim(entry, args, output)?;
    let (active, degrees) = self.trace_shape(&traces)?;
    self.check_shape(&active, &degrees)?;
    Ok(self.system.prove_streaming(&self.key, &claim, traces))
  }

  /// Verify using trusted compilation and the public call alone. No execution
  /// record, hints, witness matrices or prover-supplied table data are read.
  pub fn verify(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    proof: &Proof,
  ) -> Result<(), String> {
    self.require_committed()?;
    if self.segmented_memory {
      return Err("segmented memory requires a batch proof".into());
    }
    let claim = self.claim(entry, args, output)?;
    self.check_shape(&proof.active, &proof.log_degrees)?;
    self
      .system
      .verify(&claim, proof)
      .map_err(|e| format!("STARK verification failed: {e:?}"))
  }
}

fn build_claim<B: WitnessField>(
  plan: &TracePlan<'_, B>,
  entry: &str,
  args: &[B::Element],
  output: &[B::Element],
) -> Result<Vec<Val>, String> {
  let id = plan.program.entry(entry)?.function;
  let chip = &plan.artifact.chips[plan.members[id]];
  let (inputs, depth) = plan.entry_args(id, args);
  plan.program.inputs[id].validate(inputs, plan.program.field)?;
  plan.program.outputs[id].validate(output, plan.program.field)?;
  if chip.depth.column.is_some() && depth.is_none() {
    return Err(format!(
      "{entry} is recursive: its public claim needs a depth word after its arguments"
    ));
  }
  Ok(
    [CALL, plan.callables[&chip.name] as u64]
      .into_iter()
      .map(Val::from_u64)
      .chain(inputs.iter().copied().map(B::into_stark))
      .chain(depth.map(B::into_stark))
      .chain(output.iter().copied().map(B::into_stark))
      .collect(),
  )
}

fn auxiliary_counts_for<B: WitnessField>(
  plan: &TracePlan<'_, B>,
  record: &Execution<B>,
  ranges: &RangeCounts,
) -> Result<Vec<Vec<u64>>, String> {
  let program = &plan.program.program;
  let counts = |mi: usize| {
    let map = record.queries.tables[program.functions.len() + mi]
      .static_map
      .as_ref()
      .ok_or("missing fixed-table record")?;
    if map.counts.iter().any(|&count| count >= Val::ORDER_U64) {
      return Err("table count reaches field characteristic".into());
    }
    Ok::<_, String>(map.counts.to_vec())
  };
  #[cfg(feature = "parallel")]
  let table_counts = (0..program.maps.len())
    .into_par_iter()
    .map(counts)
    .collect::<Result<_, _>>()?;
  #[cfg(not(feature = "parallel"))]
  let table_counts =
    (0..program.maps.len()).map(counts).collect::<Result<_, _>>()?;
  let mut table_counts: Vec<Vec<u64>> = table_counts;
  for (table, range) in plan.depth.tables.iter().enumerate() {
    let uses = ranges.table(table);
    let counts = &mut table_counts[range.map - program.functions.len()];
    if uses.len() > counts.len() {
      return Err("depth range counts exceed their table".into());
    }
    for (count, &n) in counts.iter_mut().zip(uses) {
      *count = count
        .checked_add(n)
        .filter(|&c| c < Val::ORDER_U64)
        .ok_or("table count reaches field characteristic")?;
    }
  }
  if record.memory.iter().any(|entry| entry.multiplicity >= Val::ORDER_U64) {
    return Err("ROM count reaches field characteristic".into());
  }
  Ok(table_counts)
}

fn trace_shape_for(
  circuits: &[multi_stark::system::Circuit<Val>],
  traces: &[RowMajorMatrix<Val>],
  device: &[Option<usize>],
) -> Result<(Vec<bool>, Vec<u8>), String> {
  if traces.len() != circuits.len() {
    return Err("wrong circuit count".into());
  }
  let mut active = vec![];
  let mut degrees = vec![];
  for (ci, (trace, circuit)) in traces.iter().zip(circuits).enumerate() {
    let height =
      device.get(ci).copied().flatten().unwrap_or_else(|| trace.height());
    if trace.width != circuit.main_width
      || !trace.values.len().is_multiple_of(trace.width)
      || (height != 0 && !height.is_power_of_two())
    {
      return Err("invalid main trace shape".into());
    }
    active.push(height != 0);
    if height != 0 {
      degrees.push(
        u8::try_from(height.ilog2()).ok().ok_or("trace height log overflow")?,
      );
    }
  }
  Ok((active, degrees))
}

#[allow(clippy::too_many_arguments)]
fn check_shape_for(
  circuits: &[multi_stark::system::Circuit<Val>],
  members_len: usize,
  tables_len: usize,
  rom: &rom::Rom,
  log_blowup: usize,
  extra_blowup_bits: usize,
  min_log_degree: usize,
  active: &[bool],
  degrees: &[u8],
) -> Result<(), String> {
  if active.len() != circuits.len() || !active.contains(&true) {
    return Err("invalid circuit activation".into());
  }
  let mut degrees = degrees.iter();
  let mut budget = 1u64; // one public root
  let mut rows = 0u64;
  let rom_start = members_len + tables_len;
  for (ci, (circuit, &on)) in circuits.iter().zip(active).enumerate() {
    if !on {
      if circuit.preprocessed_height != 0 {
        return Err("inactive fixed table".into());
      }
      continue;
    }
    let log = *degrees.next().ok_or("missing trace height")?;
    if usize::from(log) < min_log_degree {
      return Err(format!(
        "circuit {ci} log degree {log} is below minimum {min_log_degree}"
      ));
    }
    // Goldilocks has 2-adicity 32. Include the commitment blowup (plus 1 for
    // v6-zk's 2x odd-coset hiding PCS).
    if usize::from(log) + extra_blowup_bits + log_blowup > 32 {
      return Err("trace domain exceeds Goldilocks capacity".into());
    }
    let height = 1u64 << log;
    if circuit.preprocessed_height != 0
      && circuit.preprocessed_height as u64 != height
    {
      return Err("fixed table height mismatch".into());
    }
    let weight = if ci >= rom_start {
      rom.lanes_for_width(rom.widths[ci - rom_start]) as u64
    } else {
      1
    };
    rows = height
      .checked_mul(weight)
      .and_then(|w| rows.checked_add(w))
      .filter(|&r| r <= MAX_BATCH_ROWS)
      .ok_or("trace rows exceed the batch row bound (2^39)")?;
    budget = height
      .checked_mul(circuit.num_lookups.max(1) as u64)
      .and_then(|n| budget.checked_add(n))
      .filter(|&n| n < Val::ORDER_U64)
      .ok_or("lookup count reaches field characteristic")?;
  }
  if degrees.next().is_some() {
    return Err("extra trace heights".into());
  }
  Ok(())
}
