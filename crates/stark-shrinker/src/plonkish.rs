//! Compact Plonkish Native `Fp^3` STARK Shrinker (`--stark-128` & `--stark-128-zk`).
//!
//! Compiles the Protocol `v6` (`Fp^3`, `FriBatching::Tensor`, domain-separated
//! BLAKE3) Plonkish FRI verifier from `ix-proof-compression` directly into a
//! compact `multi-stark` system (`GoldilocksBlake3V6Config` or
//! `GoldilocksBlake3V6ZkConfig`), avoiding the 45-circuit Aiur recursive VM
//! overhead while preserving full 128-bit finite-`m` Johnson + 80-bit provable
//! unique-decoding + 220-bit conjectured soundness and all `v6-zk` hiding
//! invariants.

use crate::{
  breakdown::{ProofBreakdown, analyze_v6, analyze_v6_zk},
  circuit_merge::MergedLayout,
  compact_codec,
  envelope::{
    ENVELOPE_MAGIC, EXTENSION_DEGREE, FRI_BATCHING_TENSOR, PROTOCOL_VERSION,
    ShrinkMode,
  },
};
use aiur::trace::stark::{
  BatchProof as AiurBatchProof, VerifyingKey as AiurVerifyingKey,
};
use ix_proof_compression::{
  fri::{
    Envelope as FriEnvelope, ImplementationOptions, ProofEnvelope,
    ProofProfile, Statement, StatementSlot, VerifierKey, VerifierLimits,
    VerifierPlan,
  },
  pipeline::FixedRoot,
};
use multi_stark::{
  batch::BatchProof,
  config::ProofConfig,
  lookup::{MAX_LOOKUP_GROUP, logup_max_degree, stage2_width},
  p3_adapter::{
    domain_blake3::Blake3Domain,
    fri_batching::FriBatching,
    zk::{ZK_RANDOMIZER_WIDTH, min_zk_log_degree},
  },
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::{Matrix, dense::RowMajorMatrix},
  plonkish::{Assignment, Circuit, MultiStarkCircuit},
  prover::Proof,
  system::{
    CircuitInputs, ProverKey, System, compute_vk_digest,
    compute_vk_digest_with_domain, extension_params,
  },
  types::{
    CommitmentParameters, ExtVal3, FriParameters, GoldilocksBlake3V6Config,
    GoldilocksBlake3V6ZkConfig, Val,
  },
};
use std::time::Instant;

/// Plonkish `IXSTARK6\0` envelope schema version (`v2` distinguishes Plonkish
/// compact envelopes from `v1` Aiur `.ixa` envelopes).
pub const PLONKISH_ENVELOPE_VERSION: u16 = 2;

/// Maximum number of recursive Plonkish hops permitted in an `IXSTARK6\0` v2
/// envelope (`1` direct hop for small roots, up to `4` automatic hops for
/// full-scale 59-circuit Protocol `v6` `FixedRoot` aggregate roots).
pub const MAX_PLONKISH_HOPS: u8 = 4;

/// Domain separation context for Plonkish shrinker verifying-key pinning.
const PLONKISH_VK_CONTEXT: &str = "ix/stark-shrinker/plonkish/v2/vk";

/// Namespace byte for Plonkish-to-multi-stark lowering (matches `FRI_NAMESPACE`).
const PLONKISH_NAMESPACE: u8 = 107;

/// Fixed binary header size for `IXSTARK6\0` v2 (Plonkish) envelopes.
pub const PLONKISH_HEADER_LEN: usize = 9 // magic
  + 2 // envelope_version (2)
  + 2 // protocol_version (6)
  + 2 // extension_degree (3)
  + 1 // mode_tag (1=v6, 2=v6-zk)
  + 1 // fri_batching (1=Tensor)
  + 1 // payload_codec (0=bincode, 1=compact_v1)
  + 1 // hops (1..=MAX_PLONKISH_HOPS)
  + 2 * 9 // lb, cap, lfp, mla, q, cpow, qpow, zk_randomizer_width, min_log_degree
  + 32 * 3 // shrinker_vk_digest, inner_vk_digest, claim_digest
  + 8; // proof_len

/// The outer FRI shapes [`OuterFriParams::check`] admits: folding arity up to
/// 8 (`max_log_arity <= 3`), a final polynomial of up to `2^8` coefficients,
/// and (for every shape) a single Merkle root, `cap_height = 0`.
pub const OUTER_SHAPE_LIMITS: stark_key::security::ShapeLimits =
  stark_key::security::ShapeLimits {
    max_log_arity: 3,
    max_log_final_poly_len: 8,
  };

/// The (mode, outer FRI parameters) pairs an Endpoint 1 (`IXSTARK6` v2)
/// verifier admits: the two presets `ix compress --stark-128[-zk]` produces
/// (default [`OuterFriParams::COMPACT_400KB_BALANCED`], `--compact`
/// [`OuterFriParams::ULTRA_COMPACT_400KB_ZK`]) in both modes. The verifier
/// derives its outer system from these constants; an envelope declaring any
/// other parameters is rejected.
pub const ENDPOINT1_PROFILES: [(ShrinkMode, OuterFriParams); 4] = [
  (ShrinkMode::Stark128, OuterFriParams::COMPACT_400KB_BALANCED),
  (ShrinkMode::Stark128, OuterFriParams::ULTRA_COMPACT_400KB_ZK),
  (ShrinkMode::Stark128Zk, OuterFriParams::COMPACT_400KB_BALANCED),
  (ShrinkMode::Stark128Zk, OuterFriParams::ULTRA_COMPACT_400KB_ZK),
];

/// The admitted `(mode, params)` pair equal to an envelope header's, taken
/// from `admitted` (the verifier's constants), or an error naming the
/// admitted profiles.
pub fn admitted_profile(
  header: &PlonkishHeader,
  admitted: &[(ShrinkMode, OuterFriParams)],
) -> Result<(ShrinkMode, OuterFriParams), String> {
  admitted
    .iter()
    .copied()
    .find(|&(mode, params)| mode == header.mode && params == header.params)
    .ok_or_else(|| {
      format!(
        "{} envelope under outer FRI parameters {:?} is not an admitted Endpoint 1 profile (admitted: {admitted:?})",
        header.mode.cli_flag(),
        header.params
      )
    })
}

/// The layout invariant that keeps multi-stark's Merkle-cap weakness for
/// matrices shorter than the cap layer away from Endpoint 1: the
/// final outer system is exactly one circuit whose height is fixed by its
/// preprocessed matrix (so every multi-matrix commitment holds matrices of
/// one height, which the verifier pins), and that height's LDE reaches the
/// cap layer. `OuterFriParams::check` additionally requires `cap_height = 0`.
fn check_endpoint1_outer_layout(
  definitions: &[CircuitInputs<Val>],
  params: OuterFriParams,
) -> Result<(), String> {
  let [def] = definitions else {
    return Err(format!(
      "Endpoint 1 outer system must be exactly one circuit (got {})",
      definitions.len()
    ));
  };
  let Some(prep) = def.preprocessed.as_ref() else {
    return Err(
      "Endpoint 1 outer circuit has no preprocessed matrix fixing its height"
        .into(),
    );
  };
  let height = prep.height();
  if !height.is_power_of_two() {
    return Err(format!(
      "Endpoint 1 outer circuit height {height} is not a power of two"
    ));
  }
  let lde_log = (height.ilog2() as usize)
    .checked_add(params.log_blowup)
    .ok_or("Endpoint 1 outer LDE height overflow")?;
  if lde_log < params.cap_height {
    return Err(format!(
      "Endpoint 1 outer circuit LDE height 2^{lde_log} is below the cap layer 2^{}",
      params.cap_height
    ));
  }
  Ok(())
}

/// Generalized outer FRI parameters for out-of-circuit verification of shrunk
/// Protocol `v6` and `v6-zk` STARK proofs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OuterFriParams {
  pub log_blowup: usize,
  pub num_queries: usize,
  pub commit_proof_of_work_bits: usize,
  pub query_proof_of_work_bits: usize,
  pub cap_height: usize,
  pub max_log_arity: usize,
  pub log_final_poly_len: usize,
}

impl OuterFriParams {
  /// Legacy binary-FRI compact 128-bit profile (`lb=4, q=66, qpow=20`,
  /// `cap=0, max_log_arity=1, log_final_poly_len=8`).
  ///
  /// - 149.03b finite-`m` Johnson (`m=16`)
  /// - 80.19b provable unique-decoding (`CertiFRI`)
  /// - 284b conjectured ethSTARK
  /// - 100% CUDA-compatible (`cap_height=0, max_log_arity=1`)
  /// - Measured 1-circuit size: `~600 KiB` (`v6`) / `~695 KiB` (`v6-zk`)
  pub const CUDA_COMPACT_128: Self = Self {
    log_blowup: 4,
    num_queries: 66,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 20,
    cap_height: 0,
    max_log_arity: 1,
    log_final_poly_len: 8,
  };

  /// Fast sub-400 KiB 128-bit profile using 8-ary FRI folding + `lfp=8`
  /// (`lb=4, q=62, qpow=24`: 145.21b Johnson, 80.54b UD, 272b conjectured).
  ///
  /// - 100% CUDA-compatible (`cap_height=0, max_log_arity=3`, multi-ary CUDA FRI)
  /// - Measured 1-circuit size: `385.3 KiB` (`v6`) / `430.7 KiB` (`v6-zk`)
  /// - ~1s PoW grinding on CPU, ~3.5 ms verify
  pub const COMPACT_400KB_FAST: Self = Self {
    log_blowup: 4,
    num_queries: 62,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 24,
    cap_height: 0,
    max_log_arity: 3,
    log_final_poly_len: 8,
  };

  /// Default balanced ~360–405 KiB 128-bit profile using 8-ary FRI folding + `lfp=8`
  /// (`lb=4, q=58, qpow=28`: 141.39b Johnson, 80.90b UD, 260b conjectured).
  ///
  /// - 100% CUDA-compatible (`cap_height=0, max_log_arity=3`, multi-ary CUDA FRI)
  /// - Default profile for `ix compress --stark-128` and `--stark-128-zk`
  /// - Measured 1-circuit size: `361.5 KiB` (`v6`) / `404.7 KiB` (`v6-zk`)
  pub const COMPACT_400KB_BALANCED: Self = Self {
    log_blowup: 4,
    num_queries: 58,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 28,
    cap_height: 0,
    max_log_arity: 3,
    log_final_poly_len: 8,
  };

  /// Ultra-compact sub-400 KiB profile for BOTH `v6` and `v6-zk`
  /// (`lb=4, q=55, qpow=30`: 137.53b Johnson, 80.16b UD, 250b conjectured).
  ///
  /// - 100% CUDA-compatible (`cap_height=0, max_log_arity=3`, multi-ary CUDA FRI)
  /// - Selected by `ix compress --stark-128 --compact` and `--stark-128-zk --compact`
  /// - Measured 1-circuit size: `344.1 KiB` (`v6`) / `389.1 KiB` (`v6-zk`)
  pub const ULTRA_COMPACT_400KB_ZK: Self = Self {
    log_blowup: 4,
    num_queries: 55,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 30,
    cap_height: 0,
    max_log_arity: 3,
    log_final_poly_len: 8,
  };

  /// In-circuit verifiable Hop-1 profile (`cap=0, mla=1, lfp=0`, `lb=4, q=66, qpow=20`),
  /// accepted by `ix_proof_compression::fri::VerifierPlan`.
  pub const HOP1_DEFAULT: Self = Self {
    log_blowup: 4,
    num_queries: 66,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 20,
    cap_height: 0,
    max_log_arity: 1,
    log_final_poly_len: 0,
  };

  /// Fast 128-bit in-circuit verifiable intermediate hop profile
  /// (`lb=2, q=128, qpow=20, cap=0, mla=1, lfp=0`: 142.24b Johnson,
  /// 106.78b UD, 276b conjectured). Used for wide/tall intermediate hops
  /// (`>= 2^25` rows or unmerged sharded Stage-0 FRI) where `lb=2` fits
  /// cleanly in VRAM and host RAM.
  pub const HOP_INTERMEDIATE_FAST: Self = Self {
    log_blowup: 2,
    num_queries: 128,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 20,
    cap_height: 0,
    max_log_arity: 1,
    log_final_poly_len: 0,
  };

  /// Compact 128-bit in-circuit verifiable intermediate hop profile
  /// (`lb=4, q=58, qpow=28, cap=0, mla=1, lfp=0`: 141.39b Johnson,
  /// 80.90b UD, 260b conjectured). Shrinks a 1-circuit `2^24` intermediate
  /// proof down to `~696 KiB` so the final 1-circuit C2 hop packs into `2^23`.
  pub const HOP_INTERMEDIATE_COMPACT: Self = Self {
    log_blowup: 4,
    num_queries: 58,
    commit_proof_of_work_bits: 0,
    query_proof_of_work_bits: 28,
    cap_height: 0,
    max_log_arity: 1,
    log_final_poly_len: 0,
  };

  pub const fn commitment(self) -> CommitmentParameters {
    CommitmentParameters {
      log_blowup: self.log_blowup,
      cap_height: self.cap_height,
    }
  }

  pub const fn fri(self) -> FriParameters {
    FriParameters {
      log_final_poly_len: self.log_final_poly_len,
      max_log_arity: self.max_log_arity,
      num_queries: self.num_queries,
      commit_proof_of_work_bits: self.commit_proof_of_work_bits,
      query_proof_of_work_bits: self.query_proof_of_work_bits,
    }
  }

  pub const fn johnson_millibits(self) -> usize {
    stark_key::security::johnson_millibits(&self.commitment(), &self.fri())
  }

  pub const fn provable_ud_millibits(self) -> Option<usize> {
    stark_key::security::provable_ud_millibits(&self.commitment(), &self.fri())
  }

  pub const fn conjectured_bits(self) -> usize {
    stark_key::security::conjectured_bits(&self.commitment(), &self.fri())
  }

  /// Whether these outer FRI parameters are supported by `multi-stark`'s CUDA
  /// backend (`cap_height == 0 && (1..=4).contains(&self.max_log_arity)`).
  pub const fn is_cuda_compatible(self) -> bool {
    self.cap_height == 0 && self.max_log_arity >= 1 && self.max_log_arity <= 4
  }

  /// Enforce the Protocol `v6` production floor on these exact values
  /// (`stark_key::security::check_with_shape` with [`OUTER_SHAPE_LIMITS`]):
  /// - `cap_height = 0` (single-root commitments)
  /// - `max_log_arity in 1..=3`, `log_final_poly_len <= 8`
  /// - `log_blowup in 1..=4`, `commit_pow <= 32`, `query_pow <= 32`
  /// - query-phase floors: `>= 128.000b` finite-`m` (`m=16`) Johnson,
  ///   `>= 80.000b` unique-decoding, `>= 220b` conjectured
  ///
  /// The floors count the FRI query phase only and are paper bounds; no
  /// machine-checked theorem covers folding by more than two.
  pub fn check(self) -> Result<(), String> {
    stark_key::security::check_with_shape(
      &self.commitment(),
      &self.fri(),
      OUTER_SHAPE_LIMITS,
    )
    .map_err(|e| format!("outer FRI parameters rejected: {e}"))
  }

  /// Check mode-specific `v6` / `v6-zk` invariants plus CUDA constraints when
  /// a GPU device is requested or the `cuda` feature is enabled.
  pub fn check_for_mode(
    self,
    mode: ShrinkMode,
    device: Option<i32>,
  ) -> Result<(), String> {
    self.check()?;
    if mode.is_zk() && self.log_blowup < 3 {
      return Err(format!(
        "v6-zk Plonkish shrinker requires log_blowup >= 3 (got {})",
        self.log_blowup
      ));
    }
    if cfg!(feature = "cuda") && !self.is_cuda_compatible() {
      return Err(format!(
        "CUDA builds require cap_height=0 and max_log_arity in 1..=4 (got cap_height={}, max_log_arity={})",
        self.cap_height, self.max_log_arity
      ));
    }
    if device.is_some() && !cfg!(feature = "cuda") {
      return Err(
        "GPU device requested from a CPU-only build; enable feature `cuda`"
          .into(),
      );
    }
    Ok(())
  }
}

/// Lowering and encoding options for the Plonkish STARK shrinker.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlonkishOptions {
  pub max_trace_height: usize,
  pub compact_blake3: bool,
  pub merge_tables: bool,
  pub merge_blake3_and_tables: bool,
  /// Align auxiliary/tail trace heights to `max_log - k * max_log_arity` to
  /// eliminate forced low-arity FRI rounds.
  pub align_heights_to_fri_arity: bool,
  /// When `Comp` exceeds `B3_All`'s height by <= 3x, cap `Comp` shards at
  /// `B3_All`'s height to eliminate the tallest forced binary FRI round and
  /// reduce `max_log` by 1 (adding at most 3 width-3 main columns).
  pub cap_comp_to_b3_height: bool,
  /// Horizontally pack all merged circuits (`Comp`, `B3_All`, `UnifiedTable`)
  /// into ONE single uniform-height `multi-stark` circuit (`num_circuits == 1`),
  /// yielding 1 quotient polynomial, 1 height group, and zero `acc_mask` in `v6-zk`.
  pub pack_single_circuit: bool,
  pub retune_lookup_groups: bool,
  pub compact_encoding: bool,
}

impl Default for PlonkishOptions {
  fn default() -> Self {
    Self {
      max_trace_height: 1 << 24,
      compact_blake3: true,
      merge_tables: true,
      merge_blake3_and_tables: true,
      align_heights_to_fri_arity: true,
      cap_comp_to_b3_height: true,
      pack_single_circuit: true,
      retune_lookup_groups: true,
      compact_encoding: true,
    }
  }
}

/// Public claim template extracted from a lowered `MultiStarkCircuit<Val>`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClaimSchema {
  template: Vec<Vec<Val>>,
  locations: Vec<(usize, usize)>,
}

impl ClaimSchema {
  fn from_lowered(
    compiled: &MultiStarkCircuit<Val>,
    public_count: usize,
  ) -> Result<Self, String> {
    let claims = compiled
      .claims(&vec![Val::ZERO; public_count])
      .map_err(|e| format!("plonkish claim template failed: {e}"))?;
    if claims.len() <= public_count {
      return Err("plonkish claim template shorter than public count".into());
    }
    let mut template = claims;
    let locations: Vec<(usize, usize)> =
      (1..=public_count).map(|i| (i, 3)).collect();
    for &(row, col) in &locations {
      if template[row].len() <= col {
        return Err("invalid plonkish claim row width".into());
      }
      template[row][col] = Val::ZERO;
    }
    Ok(Self { template, locations })
  }

  pub fn materialize(&self, publics: &[Val]) -> Result<Vec<Vec<Val>>, String> {
    if publics.len() != self.locations.len() {
      return Err(format!(
        "public input length {} != expected {}",
        publics.len(),
        self.locations.len()
      ));
    }
    let mut out = self.template.clone();
    for (&(row, col), &val) in self.locations.iter().zip(publics) {
      out[row][col] = val;
    }
    Ok(out)
  }

  fn hash_into(&self, hasher: &mut blake3::Hasher) {
    hasher.update(&(self.template.len() as u64).to_le_bytes());
    for row in &self.template {
      hasher.update(&(row.len() as u64).to_le_bytes());
      for &v in row {
        hasher.update(&v.as_canonical_u64().to_le_bytes());
      }
    }
    hasher.update(&(self.locations.len() as u64).to_le_bytes());
    for &(r, c) in &self.locations {
      hasher.update(&(r as u64).to_le_bytes());
      hasher.update(&(c as u64).to_le_bytes());
    }
  }
}

/// Optimal per-circuit `lookup_group_size` minimizing query opening width
/// `stage_2_width + q_col_mult * quotient_degree_for(is_zk)` while keeping
/// `quotient_degree_for(is_zk) <= blowup`.
fn tune_lookup_group_size(
  def: &mut CircuitInputs<Val>,
  blowup: usize,
  is_zk: bool,
) -> Result<(), String> {
  let params = extension_params::<GoldilocksBlake3V6Config>();
  let d = params.degree;
  let graph = def
    .compile_graph(&params)
    .map_err(|e| format!("constraint graph compile failed: {e:?}"))?;
  let num_lookups = def.lookups.len();
  if num_lookups <= 1 {
    def.lookup_group_size = 1;
    return Ok(());
  }
  let max_g = num_lookups.min(MAX_LOOKUP_GROUP);
  let q_mult = if is_zk { 2 * d } else { d };
  let mut best_g = None;
  let mut best_key = (usize::MAX, usize::MAX, usize::MAX);
  for g in 1..=max_g {
    let deg =
      graph.max_constraint_degree.max(logup_max_degree(&graph, g)) as usize;
    let q_deg = if is_zk {
      deg.max(1).next_power_of_two()
    } else {
      (deg.max(2) - 1).next_power_of_two()
    };
    if q_deg > blowup {
      continue;
    }
    let s2 = stage2_width(num_lookups, g, d);
    let total_cols = s2 + q_mult * q_deg;
    let key = (total_cols, q_deg, g);
    if key < best_key {
      best_key = key;
      best_g = Some(g);
    }
  }
  let g = best_g.ok_or_else(|| {
    format!(
      "no valid lookup_group_size fits blowup {blowup} (is_zk={is_zk}) for circuit"
    )
  })?;
  def.lookup_group_size = g;
  Ok(())
}

/// Lower a Plonkish `Circuit<Val>` into `multi-stark` circuit definitions,
/// optionally applying vertical merging of BLAKE3 + table circuits, FRI-arity
/// height alignment, and enforcing `v6-zk` minimum height & quotient degree.
fn lower_circuit_for_mode(
  circuit: Circuit<Val>,
  options: PlonkishOptions,
  mode: ShrinkMode,
  params: OuterFriParams,
) -> Result<
  (
    MultiStarkCircuit<Val>,
    Vec<CircuitInputs<Val>>,
    ClaimSchema,
    Option<MergedLayout>,
  ),
  String,
> {
  let public_count = circuit.public_values().len();
  let mut effective_max_height = options.max_trace_height;
  if options.cap_comp_to_b3_height
    && options.merge_blake3_and_tables
    && options.merge_tables
    && let Ok(layout_est) =
      circuit.multi_stark_layout_with_max_height(options.max_trace_height)
    && layout_est.custom_traces.len() == 9
  {
    // Estimate B3_All active height: t0..t3 have identical active rows <= h_0;
    // total active rows of t0..t5 is tightly bounded by sum(h_0..h_5) / 2..sum.
    let h0 = layout_est.custom_traces[0].0;
    let b3_est =
      (h0.saturating_mul(4)).next_power_of_two().min(options.max_trace_height);
    if layout_est.main_height > b3_est
      && layout_est.used_rows <= b3_est.saturating_mul(3)
      && b3_est >= (1 << 18)
    {
      effective_max_height = b3_est;
    }
  }

  let mut compiled = circuit
    .lower_to_multi_stark_sharded(
      Val::from_u8(PLONKISH_NAMESPACE),
      effective_max_height,
    )
    .map_err(|e| format!("plonkish lowering failed: {e}"))?;
  if options.merge_tables {
    compiled = compiled
      .merge_table_traces(effective_max_height)
      .map_err(|e| format!("table merging failed: {e}"))?;
  }
  let schema = ClaimSchema::from_lowered(&compiled, public_count)?;
  let raw_definitions = compiled.circuit_inputs();
  let align_arity =
    if options.align_heights_to_fri_arity { params.max_log_arity } else { 1 };
  let (mut definitions, merged_layout) =
    if options.merge_blake3_and_tables && options.merge_tables {
      let (defs, layout) = MergedLayout::try_merge(
        &compiled,
        raw_definitions,
        PLONKISH_NAMESPACE,
        options.max_trace_height,
        align_arity,
        options.pack_single_circuit,
      )?;
      (defs, Some(layout))
    } else {
      (raw_definitions, None)
    };
  finalize_definitions(&mut definitions, options, mode, params)?;

  Ok((compiled, definitions, schema, merged_layout))
}

fn finalize_definitions(
  definitions: &mut [CircuitInputs<Val>],
  options: PlonkishOptions,
  mode: ShrinkMode,
  params: OuterFriParams,
) -> Result<(), String> {
  let blowup = 1usize << params.log_blowup;
  let is_zk = mode.is_zk();
  let min_zk_height = if is_zk {
    1usize << min_zk_log_degree(params.num_queries, EXTENSION_DEGREE as usize)
  } else {
    0
  };

  for (idx, def) in definitions.iter_mut().enumerate() {
    if options.retune_lookup_groups {
      tune_lookup_group_size(def, blowup, is_zk)?;
    } else {
      def.lookup_group_size = 3;
    }
    if let Some(prep) = &def.preprocessed {
      let h = prep.height();
      if is_zk && h < min_zk_height {
        return Err(format!(
          "plonkish circuit {idx} height {h} is below v6-zk min height {min_zk_height} (enable merge_tables)"
        ));
      }
      let log_h = h.ilog2() as usize;
      let effective_log_h = log_h + usize::from(is_zk);
      if params.log_final_poly_len > 0
        && effective_log_h <= params.log_final_poly_len
      {
        return Err(format!(
          "plonkish circuit {idx} effective log height {effective_log_h} must exceed log_final_poly_len {}",
          params.log_final_poly_len
        ));
      }
    }
  }
  Ok(())
}

/// Guaranteed lower bound on `B3_All` active rows from a compact-BLAKE3
/// `MultiStarkLayout`: each custom trace `t0..t5` has power-of-two padded height
/// `h`, so its active row count is strictly `> h / 2` whenever `h > 2`.
fn b3_lower_bound(
  est: &multi_stark::plonkish::MultiStarkLayout,
) -> Option<usize> {
  if est.custom_traces.len() != 9 {
    return None;
  }
  let sum: usize = est.custom_traces[..6]
    .iter()
    .map(|&(h, _, _)| if h <= 2 { 1 } else { h / 2 + 1 })
    .sum();
  Some(sum)
}

enum HopLowering {
  Final {
    compiled: MultiStarkCircuit<Val>,
    definitions: Vec<CircuitInputs<Val>>,
    schema: ClaimSchema,
    merged: Option<MergedLayout>,
  },
  Intermediate {
    compiled: MultiStarkCircuit<Val>,
    definitions: Vec<CircuitInputs<Val>>,
    schema: ClaimSchema,
    merged: Option<MergedLayout>,
    hop_params: OuterFriParams,
  },
}

fn intermediate_hop_params_for_height(height: usize) -> OuterFriParams {
  if height >= (1 << 25) {
    OuterFriParams::HOP_INTERMEDIATE_FAST
  } else {
    OuterFriParams::HOP_INTERMEDIATE_COMPACT
  }
}

/// Deterministically decide whether `circuit` lowers directly into the final
/// 1-circuit C2 STARK under `(options, mode, params)` or requires an
/// in-circuit-verifiable transparent intermediate hop (`cap=0, mla=1, lfp=0`).
///
/// Used identically by both [`shrink_fixed_root`] and
/// [`PlonkishCircuitVerifier::derive_fixed_root`] so prover and independent
/// verifier always derive the exact same hop chain without reading proof bytes.
fn plan_hop_lowering(
  circuit: Circuit<Val>,
  options: PlonkishOptions,
  mode: ShrinkMode,
  params: OuterFriParams,
  hop: u8,
) -> Result<HopLowering, String> {
  if !options.merge_blake3_and_tables
    || !options.merge_tables
    || hop >= MAX_PLONKISH_HOPS
  {
    let (compiled, definitions, schema, merged) =
      lower_circuit_for_mode(circuit, options, mode, params)?;
    return Ok(HopLowering::Final { compiled, definitions, schema, merged });
  }

  let public_count = circuit.public_values().len();
  let max_h = options.max_trace_height;
  let double_h = max_h.saturating_mul(2);
  let layout_est = circuit.multi_stark_layout_with_max_height(max_h);

  // Fast path when the layout already guarantees B3_All exceeds `max_h`
  // (e.g. real 59-circuit FixedRoot at 2^26 or Stage-0 FRI verifier at 2^25).
  let definitely_exceeds_max = match &layout_est {
    Err(_) => true,
    Ok(est) => b3_lower_bound(est).is_some_and(|lb| lb > max_h),
  };
  if definitely_exceeds_max {
    let double_est = circuit.multi_stark_layout_with_max_height(double_h);
    let try_merged_double = double_est
      .as_ref()
      .ok()
      .and_then(b3_lower_bound)
      .is_some_and(|lb| lb <= double_h);
    if try_merged_double {
      let mut compiled = circuit
        .lower_to_multi_stark_sharded(
          Val::from_u8(PLONKISH_NAMESPACE),
          double_h,
        )
        .map_err(|e| format!("hop {hop} lowering failed: {e}"))?;
      compiled = compiled
        .merge_table_traces(double_h)
        .map_err(|e| format!("hop {hop} table merge failed: {e}"))?;
      let schema = ClaimSchema::from_lowered(&compiled, public_count)?;
      let raw_defs = compiled.circuit_inputs();
      let (mut definitions, merged) = MergedLayout::try_merge(
        &compiled,
        raw_defs,
        PLONKISH_NAMESPACE,
        double_h,
        1,
        true,
      )?;
      let (merged_opt, hop_params) = if merged.is_merged() {
        (Some(merged), intermediate_hop_params_for_height(double_h))
      } else {
        (None, OuterFriParams::HOP_INTERMEDIATE_FAST)
      };
      finalize_definitions(
        &mut definitions,
        options,
        ShrinkMode::Stark128,
        hop_params,
      )?;
      return Ok(HopLowering::Intermediate {
        compiled,
        definitions,
        schema,
        merged: merged_opt,
        hop_params,
      });
    }

    // Circuit exceeds even `double_h` (e.g. 59-circuit FixedRoot -> Stage-0 FRI):
    // lower unmerged sharded at `max_h` (or `double_h` if a custom trace needed it)
    // with fast lb=2, q=128 transparent FRI.
    let unmerged_h = if layout_est.is_ok() { max_h } else { double_h };
    let mut compiled = circuit
      .lower_to_multi_stark_sharded(
        Val::from_u8(PLONKISH_NAMESPACE),
        unmerged_h,
      )
      .map_err(|e| format!("hop {hop} unmerged lowering failed: {e}"))?;
    compiled = compiled
      .merge_table_traces(unmerged_h)
      .map_err(|e| format!("hop {hop} unmerged table merge failed: {e}"))?;
    let schema = ClaimSchema::from_lowered(&compiled, public_count)?;
    let mut definitions = compiled.circuit_inputs();
    let hop_params = OuterFriParams::HOP_INTERMEDIATE_FAST;
    finalize_definitions(
      &mut definitions,
      options,
      ShrinkMode::Stark128,
      hop_params,
    )?;
    return Ok(HopLowering::Intermediate {
      compiled,
      definitions,
      schema,
      merged: None,
      hop_params,
    });
  }

  // Circuit may fit inside `max_h`: lower once with 3x comp-cap heuristic.
  let mut effective_max_height = max_h;
  if options.cap_comp_to_b3_height
    && let Ok(est) = &layout_est
    && est.custom_traces.len() == 9
  {
    let h0 = est.custom_traces[0].0;
    let b3_est = (h0.saturating_mul(4)).next_power_of_two().min(max_h);
    if est.main_height > b3_est
      && est.used_rows <= b3_est.saturating_mul(3)
      && b3_est >= (1 << 18)
    {
      effective_max_height = b3_est;
    }
  }
  let mut compiled = circuit
    .lower_to_multi_stark_sharded(
      Val::from_u8(PLONKISH_NAMESPACE),
      effective_max_height,
    )
    .map_err(|e| format!("hop {hop} lowering failed: {e}"))?;
  compiled = compiled
    .merge_table_traces(effective_max_height)
    .map_err(|e| format!("hop {hop} table merge failed: {e}"))?;
  let schema = ClaimSchema::from_lowered(&compiled, public_count)?;
  let raw_defs = compiled.circuit_inputs();
  let align_arity =
    if options.align_heights_to_fri_arity { params.max_log_arity } else { 1 };
  let (mut definitions, merged) = MergedLayout::try_merge(
    &compiled,
    raw_defs,
    PLONKISH_NAMESPACE,
    max_h,
    align_arity,
    options.pack_single_circuit,
  )?;

  if !merged.is_merged() {
    // Exact B3_All active height exceeded `max_h`; retry merging at `double_h`
    // without re-lowering (try_merge returned `definitions` unmodified).
    let (mut defs2, merged2) = MergedLayout::try_merge(
      &compiled,
      definitions,
      PLONKISH_NAMESPACE,
      double_h,
      1,
      true,
    )?;
    let (merged_opt, hop_params) = if merged2.is_merged() {
      (Some(merged2), intermediate_hop_params_for_height(double_h))
    } else {
      (None, OuterFriParams::HOP_INTERMEDIATE_FAST)
    };
    finalize_definitions(
      &mut defs2,
      options,
      ShrinkMode::Stark128,
      hop_params,
    )?;
    return Ok(HopLowering::Intermediate {
      compiled,
      definitions: defs2,
      schema,
      merged: merged_opt,
      hop_params,
    });
  }

  // In multi-hop mode (`hop > 1`), if a 2^24 intermediate verifier lands right
  // at `max_h >= 2^24` and another hop remains, insert one compact intermediate
  // hop (`HOP_INTERMEDIATE_COMPACT`) so the final 1-circuit C2 hop drops to
  // 2^23 (halving final proving RAM/time so even `--stark-128-zk` fits 249 GiB).
  let max_packed_h = definitions
    .iter()
    .map(|d| d.preprocessed.as_ref().map_or(0, Matrix::height))
    .max()
    .unwrap_or(0);
  if hop > 1 && max_packed_h >= max_h && max_h >= (1 << 24) {
    let hop_params = OuterFriParams::HOP_INTERMEDIATE_COMPACT;
    finalize_definitions(
      &mut definitions,
      options,
      ShrinkMode::Stark128,
      hop_params,
    )?;
    return Ok(HopLowering::Intermediate {
      compiled,
      definitions,
      schema,
      merged: Some(merged),
      hop_params,
    });
  }

  finalize_definitions(&mut definitions, options, mode, params)?;
  Ok(HopLowering::Final { compiled, definitions, schema, merged: Some(merged) })
}

fn next_hop_verifier_plan<'a>(
  vk: &'a VerifierKey,
  schema: &ClaimSchema,
) -> Result<(VerifierPlan<'a>, Statement<StatementSlot>, ProofProfile), String>
{
  let num_circuits = vk.system().circuits.len();
  let log_degrees: Vec<u8> = vk
    .system()
    .circuits
    .iter()
    .map(|c| {
      u8::try_from(c.preprocessed_height.ilog2())
        .map_err(|err| format!("intermediate hop log_degree overflow: {err}"))
    })
    .collect::<Result<_, _>>()?;
  let profile = ProofProfile {
    envelope: FriEnvelope::Ordinary,
    active: vec![true; num_circuits],
    log_degrees,
    claim_lengths: schema.template.iter().map(Vec::len).collect(),
    message_lengths: vec![],
    max_field_retries: ix_proof_compression::fri::DEFAULT_FIELD_RETRIES,
  };
  let mut stmt_schema = Statement {
    claims: schema
      .template
      .iter()
      .map(|row| row.iter().copied().map(StatementSlot::Constant).collect())
      .collect(),
    messages: vec![],
  };
  for &(r, c) in &schema.locations {
    stmt_schema.claims[r][c] = StatementSlot::Public;
  }
  let plan =
    VerifierPlan::validate(vk, profile.clone(), VerifierLimits::default())
      .map_err(|e| format!("intermediate hop verifier plan invalid: {e}"))?;
  Ok((plan, stmt_schema, profile))
}

#[allow(clippy::too_many_arguments)]
fn prove_intermediate_hop(
  compiled: MultiStarkCircuit<Val>,
  definitions: Vec<CircuitInputs<Val>>,
  schema: &ClaimSchema,
  merged: Option<&MergedLayout>,
  assignment: Assignment<Val>,
  expected_publics: &[Val],
  hop_params: OuterFriParams,
  options: PlonkishOptions,
  hop: u8,
  device: Option<i32>,
) -> Result<(Circuit<Val>, Assignment<Val>), String> {
  hop_params.check_for_mode(ShrinkMode::Stark128, device)?;
  let claims = schema.materialize(expected_publics)?;
  let config = GoldilocksBlake3V6Config::with_device(
    hop_params.commitment(),
    hop_params.fri(),
    FriBatching::Tensor,
    device,
  );
  let (sys, key) = System::new_without_preprocessed(config, definitions);
  let stage1 = if let Some(layout) = merged
    && layout.is_merged()
  {
    let traces = layout.build_traces(&compiled, &assignment)?;
    drop(compiled);
    drop(assignment);
    sys.prove_stage_1_streaming(traces)
  } else {
    let shards = compiled
      .trace_shards(&assignment)
      .map_err(|e| format!("hop {hop} trace shards failed: {e}"))?;
    let count = sys.circuits.len();
    let mut trace_err: Option<String> = None;
    let s1 =
      sys.prove_stage_1_streaming((0..count).map(
        |ci| match shards.trace(ci) {
          Ok(t) => t,
          Err(e) => {
            if trace_err.is_none() {
              trace_err = Some(format!("hop {hop} trace {ci}: {e}"));
            }
            RowMajorMatrix::new(Vec::new(), sys.circuits[ci].main_width)
          },
        },
      ));
    if let Some(err) = trace_err {
      return Err(err);
    }
    drop(compiled);
    drop(assignment);
    s1
  };
  let refs: Vec<&[Val]> = claims.iter().map(Vec::as_slice).collect();
  let proof = sys.prove_committed(&key, &refs, stage1);
  drop(key);
  #[cfg(feature = "cuda")]
  multi_stark::cuda::release_device_memory();
  sys
    .verify_multiple_claims(&refs, &proof)
    .map_err(|e| format!("hop {hop} self-verify failed: {e:?}"))?;

  let hop_vk = VerifierKey::new(sys);
  let (plan, stmt_schema, profile) = next_hop_verifier_plan(&hop_vk, schema)?;
  if proof.active != profile.active || proof.log_degrees != profile.log_degrees
  {
    return Err(format!(
      "hop {hop} proof profile mismatch (active/log_degrees)"
    ));
  }
  let (next_circuit, inputs) = plan
    .build(
      stmt_schema,
      ImplementationOptions { compact_blake3: options.compact_blake3 },
    )
    .map_err(|e| format!("hop {} circuit build failed: {e}", hop + 1))?;
  let expanded = plan
    .expand_witness(ProofEnvelope::Ordinary { proof: &proof, claims: &claims })
    .map_err(|e| format!("hop {} witness expansion failed: {e}", hop + 1))?;
  let mut witness = next_circuit.witness();
  inputs
    .assign_statement(&mut witness, &Statement { claims, messages: vec![] })
    .map_err(|e| format!("hop {} statement assign failed: {e}", hop + 1))?;
  expanded
    .assign_proof(&mut witness, &inputs)
    .map_err(|e| format!("hop {} proof assign failed: {e}", hop + 1))?;
  let next_assignment = witness
    .generate()
    .map_err(|e| format!("hop {} witness generate failed: {e}", hop + 1))?;
  if next_assignment.public_values() != expected_publics {
    return Err(format!(
      "hop {} public statement mismatch with expected claim",
      hop + 1
    ));
  }
  Ok((next_circuit, next_assignment))
}

#[allow(clippy::too_many_arguments)]
fn compute_plonkish_vk_digest(
  mode: ShrinkMode,
  params: OuterFriParams,
  compact_encoding: bool,
  hops: u8,
  zk_randomizer_width: usize,
  min_log_degree: usize,
  system_vk_digest: &[u8; 32],
  preprocessed_roots: Option<&[[u8; 32]]>,
  schema: &ClaimSchema,
) -> Result<[u8; 32], String> {
  let mut hasher = blake3::Hasher::new_derive_key(PLONKISH_VK_CONTEXT);
  hasher.update(&PLONKISH_ENVELOPE_VERSION.to_le_bytes());
  hasher.update(&PROTOCOL_VERSION.to_le_bytes());
  hasher.update(&EXTENSION_DEGREE.to_le_bytes());
  hasher.update(&[mode.tag(), FRI_BATCHING_TENSOR]);
  hasher.update(&[u8::from(compact_encoding), hops]);
  for value in [
    params.log_blowup,
    params.cap_height,
    params.log_final_poly_len,
    params.max_log_arity,
    params.num_queries,
    params.commit_proof_of_work_bits,
    params.query_proof_of_work_bits,
    zk_randomizer_width,
    min_log_degree,
  ] {
    let word = u16::try_from(value)
      .map_err(|err| format!("VK parameter {value} exceeds u16: {err}"))?;
    hasher.update(&word.to_le_bytes());
  }
  hasher.update(system_vk_digest);
  match preprocessed_roots {
    None => {
      hasher.update(&[0u8]);
    },
    Some(roots) => {
      let count = u16::try_from(roots.len())
        .map_err(|err| format!("preprocessed cap roots exceed u16: {err}"))?;
      hasher.update(&[1u8]);
      hasher.update(&count.to_le_bytes());
      for root in roots {
        hasher.update(root);
      }
    },
  }
  schema.hash_into(&mut hasher);
  Ok(*hasher.finalize().as_bytes())
}

/// Parsed header of a Plonkish `IXSTARK6\0` v2 envelope.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PlonkishHeader {
  pub mode: ShrinkMode,
  pub params: OuterFriParams,
  pub compact_encoding: bool,
  pub hops: u8,
  pub zk_randomizer_width: u16,
  pub min_log_degree: u16,
  pub shrinker_vk_digest: [u8; 32],
  pub inner_vk_digest: [u8; 32],
  pub claim_digest: [u8; 32],
  pub proof_len: u64,
}

/// Verified metadata and honest trust/ZK posture for a Plonkish `IXSTARK6\0` v2
/// shrunk proof envelope.
#[derive(Clone, Debug)]
pub struct PlonkishVerifyReport {
  pub header: PlonkishHeader,
  pub envelope_bytes: usize,
  pub proof_bytes: usize,
  pub verify_ms: f64,
  pub johnson_millibits: usize,
  pub provable_ud_millibits: usize,
  pub conjectured_bits: usize,
  pub outer_circuits: usize,
}

impl PlonkishVerifyReport {
  fn build(
    header: PlonkishHeader,
    envelope_bytes: usize,
    verify_ms: f64,
    outer_circuits: usize,
  ) -> Self {
    Self {
      header,
      envelope_bytes,
      proof_bytes: envelope_bytes.saturating_sub(PLONKISH_HEADER_LEN),
      verify_ms,
      johnson_millibits: header.params.johnson_millibits(),
      provable_ud_millibits: header.params.provable_ud_millibits().unwrap_or(0),
      conjectured_bits: header.params.conjectured_bits(),
      outer_circuits,
    }
  }

  /// Format a concise, honest trust and zero-knowledge banner for CLI output.
  pub fn banner(&self) -> String {
    let j_w = self.johnson_millibits / 1000;
    let j_f = (self.johnson_millibits % 1000) / 10;
    let u_w = self.provable_ud_millibits / 1000;
    let u_f = (self.provable_ud_millibits % 1000) / 10;
    let p = self.header.params;
    let zk_line = match self.header.mode {
      ShrinkMode::Stark128 => {
        "NON-ZK (transparent witness — no hiding PCS or leaf salting)"
          .to_owned()
      },
      ShrinkMode::Stark128Zk => format!(
        "BLINDED (v6-zk hiding-PCS construction: 2x odd-coset blinding, W_R={}, 16-byte BLAKE3-CTR leaf salts, telescoping quotient blinding, {} outer circuit(s), min_log_degree={}; no hiding property is stated or proved)",
        self.header.zk_randomizer_width,
        self.outer_circuits,
        self.header.min_log_degree,
      ),
    };
    format!(
      "Endpoint 1 Compact Plonkish Native Fp^3 STARK Shrinker ({flag} / {proto})\n\
       \x20 Field/PCS : Fp^3 = Fp[X]/(X^3 - X - 1) | BLAKE3 derive_key | FriBatching::Tensor | {c} outer circuit(s)\n\
       \x20 FRI query : {j_w}.{j_f:02}b finite-m Johnson (m=16) | {u_w}.{u_f:02}b unique-decoding | {conj}b conjectured; query-phase floor terms, no machine-checked theorem covers this verifier (lb={lb}, q={q}, mla={mla}, lfp={lfp}, cap={cap}, qpow={qpow})\n\
       \x20 Trust     : Transparent (zero trusted setup) | 32-byte BLAKE3: ~128-bit classical, ~85-bit quantum collision resistance\n\
       \x20 Privacy   : {zk_line}\n\
       \x20 Outer VK  : {svk} (derived by the verifier)\n\
       \x20 Inner VK  : {ivk}\n\
       \x20 Claim     : {claim}\n\
       \x20 Proof     : {env} bytes ({raw} B payload, codec={codec}, hops={hops}) | verified in {ms:.2} ms",
      flag = self.header.mode.cli_flag(),
      proto = self.header.mode.protocol_name(),
      c = self.outer_circuits,
      conj = self.conjectured_bits,
      lb = p.log_blowup,
      q = p.num_queries,
      mla = p.max_log_arity,
      lfp = p.log_final_poly_len,
      cap = p.cap_height,
      qpow = p.query_proof_of_work_bits,
      svk = blake3::Hash::from_bytes(self.header.shrinker_vk_digest).to_hex(),
      ivk = blake3::Hash::from_bytes(self.header.inner_vk_digest).to_hex(),
      claim = blake3::Hash::from_bytes(self.header.claim_digest).to_hex(),
      env = self.envelope_bytes,
      raw = self.proof_bytes,
      codec =
        if self.header.compact_encoding { "compact-v1" } else { "bincode" },
      hops = self.header.hops,
      ms = self.verify_ms,
    )
  }
}

/// Parse and strictly validate only the header of a Plonkish `IXSTARK6\0` v2
/// envelope without copying the proof payload.
pub fn peek_plonkish_header(bytes: &[u8]) -> Result<PlonkishHeader, String> {
  Ok(PlonkishEnvelope::from_bytes(bytes)?.header)
}

/// Complete Plonkish `IXSTARK6\0` v2 envelope.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PlonkishEnvelope {
  pub header: PlonkishHeader,
  pub proof_bytes: Vec<u8>,
}

fn read_u16_le(bytes: &[u8], pos: &mut usize) -> Result<u16, String> {
  let end = pos.checked_add(2).ok_or("header offset overflow")?;
  let s = bytes.get(*pos..end).ok_or("truncated Plonkish envelope header")?;
  *pos = end;
  Ok(u16::from_le_bytes([s[0], s[1]]))
}

fn read_u64_le(bytes: &[u8], pos: &mut usize) -> Result<u64, String> {
  let end = pos.checked_add(8).ok_or("header offset overflow")?;
  let s = bytes.get(*pos..end).ok_or("truncated Plonkish envelope header")?;
  *pos = end;
  Ok(u64::from_le_bytes(s.try_into().expect("8 bytes")))
}

fn read_arr32(bytes: &[u8], pos: &mut usize) -> Result<[u8; 32], String> {
  let end = pos.checked_add(32).ok_or("header offset overflow")?;
  let s = bytes.get(*pos..end).ok_or("truncated Plonkish envelope header")?;
  *pos = end;
  Ok(s.try_into().expect("32 bytes"))
}

impl PlonkishEnvelope {
  pub fn to_bytes(&self) -> Result<Vec<u8>, String> {
    let proof_len = u64::try_from(self.proof_bytes.len())
      .map_err(|err| format!("proof length exceeds u64: {err}"))?;
    if proof_len != self.header.proof_len {
      return Err("header proof_len mismatch".into());
    }
    let mut out =
      Vec::with_capacity(PLONKISH_HEADER_LEN + self.proof_bytes.len());
    out.extend_from_slice(ENVELOPE_MAGIC);
    out.extend_from_slice(&PLONKISH_ENVELOPE_VERSION.to_le_bytes());
    out.extend_from_slice(&PROTOCOL_VERSION.to_le_bytes());
    out.extend_from_slice(&EXTENSION_DEGREE.to_le_bytes());
    out.push(self.header.mode.tag());
    out.push(FRI_BATCHING_TENSOR);
    out.push(u8::from(self.header.compact_encoding));
    out.push(self.header.hops);
    for value in [
      self.header.params.log_blowup,
      self.header.params.cap_height,
      self.header.params.log_final_poly_len,
      self.header.params.max_log_arity,
      self.header.params.num_queries,
      self.header.params.commit_proof_of_work_bits,
      self.header.params.query_proof_of_work_bits,
    ] {
      let word = u16::try_from(value)
        .map_err(|err| format!("parameter {value} exceeds u16: {err}"))?;
      out.extend_from_slice(&word.to_le_bytes());
    }
    out.extend_from_slice(&self.header.zk_randomizer_width.to_le_bytes());
    out.extend_from_slice(&self.header.min_log_degree.to_le_bytes());
    out.extend_from_slice(&self.header.shrinker_vk_digest);
    out.extend_from_slice(&self.header.inner_vk_digest);
    out.extend_from_slice(&self.header.claim_digest);
    out.extend_from_slice(&proof_len.to_le_bytes());
    debug_assert_eq!(out.len(), PLONKISH_HEADER_LEN);
    out.extend_from_slice(&self.proof_bytes);
    Ok(out)
  }

  pub fn from_bytes(bytes: &[u8]) -> Result<Self, String> {
    if bytes.len() < PLONKISH_HEADER_LEN {
      return Err(format!(
        "Plonkish IXSTARK6 envelope too short ({} bytes, minimum {PLONKISH_HEADER_LEN})",
        bytes.len()
      ));
    }
    if !bytes.starts_with(ENVELOPE_MAGIC) {
      return Err("invalid magic: expected IXSTARK6\\0".into());
    }
    let mut pos = ENVELOPE_MAGIC.len();
    let version = read_u16_le(bytes, &mut pos)?;
    if version != PLONKISH_ENVELOPE_VERSION {
      return Err(format!(
        "unsupported Plonkish envelope version {version} (expected {PLONKISH_ENVELOPE_VERSION})"
      ));
    }
    let protocol_version = read_u16_le(bytes, &mut pos)?;
    if protocol_version != PROTOCOL_VERSION {
      return Err(format!(
        "unsupported STARK protocol version {protocol_version}: Protocol v5 is retired; only Protocol v6 ({PROTOCOL_VERSION}) is accepted"
      ));
    }
    let extension_degree = read_u16_le(bytes, &mut pos)?;
    if extension_degree != EXTENSION_DEGREE {
      return Err(format!(
        "unsupported extension degree {extension_degree}: Fp^2 is retired; only Fp^3 ({EXTENSION_DEGREE}) is accepted"
      ));
    }
    let mode = ShrinkMode::from_tag(bytes[pos])?;
    pos += 1;
    let fri_batching = bytes[pos];
    pos += 1;
    if fri_batching != FRI_BATCHING_TENSOR {
      return Err(format!(
        "unsupported FRI batching {fri_batching}: only FriBatching::Tensor ({FRI_BATCHING_TENSOR}) is accepted"
      ));
    }
    let compact_encoding = match bytes[pos] {
      0 => false,
      1 => true,
      other => return Err(format!("unsupported payload codec tag {other}")),
    };
    pos += 1;
    let hops = bytes[pos];
    pos += 1;
    if !(1..=MAX_PLONKISH_HOPS).contains(&hops) {
      return Err(format!("unsupported Plonkish hop count {hops}"));
    }
    let params = OuterFriParams {
      log_blowup: usize::from(read_u16_le(bytes, &mut pos)?),
      cap_height: usize::from(read_u16_le(bytes, &mut pos)?),
      log_final_poly_len: usize::from(read_u16_le(bytes, &mut pos)?),
      max_log_arity: usize::from(read_u16_le(bytes, &mut pos)?),
      num_queries: usize::from(read_u16_le(bytes, &mut pos)?),
      commit_proof_of_work_bits: usize::from(read_u16_le(bytes, &mut pos)?),
      query_proof_of_work_bits: usize::from(read_u16_le(bytes, &mut pos)?),
    };
    let zk_randomizer_width = read_u16_le(bytes, &mut pos)?;
    let min_log_degree = read_u16_le(bytes, &mut pos)?;
    let shrinker_vk_digest = read_arr32(bytes, &mut pos)?;
    let inner_vk_digest = read_arr32(bytes, &mut pos)?;
    let claim_digest = read_arr32(bytes, &mut pos)?;
    let proof_len = read_u64_le(bytes, &mut pos)?;
    debug_assert_eq!(pos, PLONKISH_HEADER_LEN);

    params.check()?;
    match mode {
      ShrinkMode::Stark128 => {
        if zk_randomizer_width != 0 || min_log_degree != 0 {
          return Err(format!(
            "transparent --stark-128 envelope must have W_R=0 and min_log_degree=0 (got {zk_randomizer_width}, {min_log_degree})"
          ));
        }
      },
      ShrinkMode::Stark128Zk => {
        if usize::from(zk_randomizer_width) != ZK_RANDOMIZER_WIDTH {
          return Err(format!(
            "unsupported v6-zk randomizer width {zk_randomizer_width} (expected {ZK_RANDOMIZER_WIDTH})"
          ));
        }
        let expected_mld =
          min_zk_log_degree(params.num_queries, EXTENSION_DEGREE as usize);
        if usize::from(min_log_degree) != expected_mld {
          return Err(format!(
            "v6-zk min_log_degree {min_log_degree} != required {expected_mld}"
          ));
        }
        if params.log_blowup < 3 {
          return Err(format!(
            "v6-zk requires log_blowup >= 3 (got {})",
            params.log_blowup
          ));
        }
      },
    }

    let proof_len_usize = usize::try_from(proof_len)
      .map_err(|err| format!("proof_len overflows usize: {err}"))?;
    if proof_len_usize == 0 {
      return Err("empty proof payload".into());
    }
    let expected_total = PLONKISH_HEADER_LEN
      .checked_add(proof_len_usize)
      .ok_or("envelope length overflow")?;
    if bytes.len() != expected_total {
      return Err(format!(
        "envelope length mismatch: header declares {expected_total}, got {}",
        bytes.len()
      ));
    }
    Ok(Self {
      header: PlonkishHeader {
        mode,
        params,
        compact_encoding,
        hops,
        zk_randomizer_width,
        min_log_degree,
        shrinker_vk_digest,
        inner_vk_digest,
        claim_digest,
        proof_len,
      },
      proof_bytes: bytes[PLONKISH_HEADER_LEN..].to_vec(),
    })
  }
}

/// Output of a Plonkish shrink operation, including self-verification report,
/// exact byte breakdown, and prover/verifier timings.
#[derive(Clone, Debug)]
pub struct PlonkishShrinkOutput {
  pub envelope_bytes: Vec<u8>,
  pub report: PlonkishVerifyReport,
  pub breakdown: ProofBreakdown,
  pub prove_ms: f64,
  pub verify_ms: f64,
  pub trace_dimensions: Vec<(usize, usize)>,
  pub vk_digest: [u8; 32],
}

enum OuterSystem {
  Transparent {
    system: System<GoldilocksBlake3V6Config>,
    key: Option<ProverKey<GoldilocksBlake3V6Config>>,
  },
  Zk {
    system: System<GoldilocksBlake3V6ZkConfig>,
    key: Option<ProverKey<GoldilocksBlake3V6ZkConfig>>,
  },
}

impl OuterSystem {
  fn build(
    definitions: Vec<CircuitInputs<Val>>,
    mode: ShrinkMode,
    params: OuterFriParams,
    device: Option<i32>,
    keep_prover_key: bool,
  ) -> Result<(Self, [u8; 32], Option<Vec<[u8; 32]>>, u16, u16), String> {
    params.check_for_mode(mode, device)?;
    match mode {
      ShrinkMode::Stark128 => {
        let config = GoldilocksBlake3V6Config::with_device(
          params.commitment(),
          params.fri(),
          FriBatching::Tensor,
          device,
        );
        let (system, key) =
          System::new_without_preprocessed(config, definitions);
        debug_assert_eq!(
          system.vk_digest,
          compute_vk_digest::<Val, ExtVal3>(&system.circuits)
        );
        let vk_d = system.vk_digest;
        let prep_roots =
          system.preprocessed_commit.as_ref().map(|c| c.roots().to_vec());
        let key = keep_prover_key.then_some(key);
        #[cfg(feature = "cuda")]
        if key.is_none() {
          multi_stark::cuda::release_device_memory();
        }
        Ok((Self::Transparent { system, key }, vk_d, prep_roots, 0, 0))
      },
      ShrinkMode::Stark128Zk => {
        let config = GoldilocksBlake3V6ZkConfig::with_options(
          params.commitment(),
          params.fri(),
          FriBatching::Tensor,
          ZK_RANDOMIZER_WIDTH,
          device,
        );
        let (system, key) =
          System::new_without_preprocessed(config, definitions);
        debug_assert_eq!(
          system.vk_digest,
          compute_vk_digest_with_domain::<Val, ExtVal3>(
            &system.circuits,
            Blake3Domain::ZkVerifyingKey,
          )
        );
        let vk_d = system.vk_digest;
        let prep_roots =
          system.preprocessed_commit.as_ref().map(|c| c.roots().to_vec());
        let rw = u16::try_from(system.config.zk_randomizer_width())
          .map_err(|err| format!("W_R exceeds u16: {err}"))?;
        let mld = u16::try_from(system.config.min_log_degree())
          .map_err(|err| format!("min_log_degree exceeds u16: {err}"))?;
        let key = keep_prover_key.then_some(key);
        #[cfg(feature = "cuda")]
        if key.is_none() {
          multi_stark::cuda::release_device_memory();
        }
        Ok((Self::Zk { system, key }, vk_d, prep_roots, rw, mld))
      },
    }
  }

  fn prove_and_drop_key(
    &mut self,
    compiled: MultiStarkCircuit<Val>,
    assignment: Assignment<Val>,
    merged: Option<&MergedLayout>,
    claims: &[Vec<Val>],
    compact_encoding: bool,
  ) -> Result<(Vec<u8>, ProofBreakdown), String> {
    let refs: Vec<&[Val]> = claims.iter().map(Vec::as_slice).collect();
    match self {
      Self::Transparent { system, key } => {
        let key = key.take().ok_or("verifier-only system cannot prove")?;
        let stage1 = if let Some(layout) = merged
          && layout.is_merged()
        {
          let traces = layout.build_traces(&compiled, &assignment)?;
          drop(compiled);
          drop(assignment);
          system.prove_stage_1_streaming(traces)
        } else {
          let shards = compiled
            .trace_shards(&assignment)
            .map_err(|e| format!("trace shards failed: {e}"))?;
          let count = system.circuits.len();
          let mut trace_err: Option<String> = None;
          let iter = (0..count).map(|ci| match shards.trace(ci) {
            Ok(t) => t,
            Err(e) => {
              if trace_err.is_none() {
                trace_err = Some(format!("trace {ci} failed: {e}"));
              }
              RowMajorMatrix::new(Vec::new(), system.circuits[ci].main_width)
            },
          });
          let s1 = system.prove_stage_1_streaming(iter);
          if let Some(err) = trace_err {
            return Err(err);
          }
          drop(compiled);
          drop(assignment);
          s1
        };
        let proof = system.prove_committed(&key, &refs, stage1);
        drop(key);
        #[cfg(feature = "cuda")]
        multi_stark::cuda::release_device_memory();
        system
          .verify_multiple_claims(&refs, &proof)
          .map_err(|e| format!("v6 self-verify failed: {e:?}"))?;
        let compact_bytes = compact_codec::encode_v6(system, &proof)?;
        let breakdown = analyze_v6(&proof, compact_bytes.len())?;
        let bytes = if compact_encoding {
          compact_bytes
        } else {
          proof
            .to_bytes()
            .map_err(|e| format!("v6 proof encode failed: {e}"))?
        };
        Ok((bytes, breakdown))
      },
      Self::Zk { system, key } => {
        let key = key.take().ok_or("verifier-only system cannot prove")?;
        let stage1 = if let Some(layout) = merged
          && layout.is_merged()
        {
          let traces = layout.build_traces(&compiled, &assignment)?;
          drop(compiled);
          drop(assignment);
          system.prove_stage_1_streaming(traces)
        } else {
          let shards = compiled
            .trace_shards(&assignment)
            .map_err(|e| format!("trace shards failed: {e}"))?;
          let count = system.circuits.len();
          let mut trace_err: Option<String> = None;
          let iter = (0..count).map(|ci| match shards.trace(ci) {
            Ok(t) => t,
            Err(e) => {
              if trace_err.is_none() {
                trace_err = Some(format!("trace {ci} failed: {e}"));
              }
              RowMajorMatrix::new(Vec::new(), system.circuits[ci].main_width)
            },
          });
          let s1 = system.prove_stage_1_streaming(iter);
          if let Some(err) = trace_err {
            return Err(err);
          }
          drop(compiled);
          drop(assignment);
          s1
        };
        let proof = system.prove_committed(&key, &refs, stage1);
        drop(key);
        #[cfg(feature = "cuda")]
        multi_stark::cuda::release_device_memory();
        system
          .verify_multiple_claims(&refs, &proof)
          .map_err(|e| format!("v6-zk self-verify failed: {e:?}"))?;
        let compact_bytes = compact_codec::encode_v6_zk(system, &proof)?;
        let breakdown = analyze_v6_zk(&proof, compact_bytes.len())?;
        let bytes = if compact_encoding {
          compact_bytes
        } else {
          proof
            .to_bytes()
            .map_err(|e| format!("v6-zk proof encode failed: {e}"))?
        };
        Ok((bytes, breakdown))
      },
    }
  }

  fn num_circuits(&self) -> usize {
    match self {
      Self::Transparent { system, .. } => system.circuits.len(),
      Self::Zk { system, .. } => system.circuits.len(),
    }
  }

  fn verify_bytes(
    &self,
    claims: &[Vec<Val>],
    proof_bytes: &[u8],
    compact_encoding: bool,
  ) -> Result<(), String> {
    let refs: Vec<&[Val]> = claims.iter().map(Vec::as_slice).collect();
    match self {
      Self::Transparent { system, .. } => {
        let proof = if compact_encoding {
          let p = compact_codec::decode_v6(system, proof_bytes)?;
          let re = compact_codec::encode_v6(system, &p)?;
          if re != proof_bytes {
            return Err("noncanonical compact v6 proof bytes".into());
          }
          p
        } else {
          let p = Proof::<GoldilocksBlake3V6Config>::from_bytes(proof_bytes)
            .map_err(|e| format!("v6 proof decode failed: {e}"))?;
          let re = p
            .to_bytes()
            .map_err(|e| format!("v6 proof re-encode failed: {e}"))?;
          if re != proof_bytes {
            return Err("noncanonical or trailing v6 proof bytes".into());
          }
          p
        };
        system
          .verify_multiple_claims(&refs, &proof)
          .map_err(|e| format!("v6 STARK verification failed: {e:?}"))
      },
      Self::Zk { system, .. } => {
        let proof = if compact_encoding {
          let p = compact_codec::decode_v6_zk(system, proof_bytes)?;
          let re = compact_codec::encode_v6_zk(system, &p)?;
          if re != proof_bytes {
            return Err("noncanonical compact v6-zk proof bytes".into());
          }
          p
        } else {
          let p = Proof::<GoldilocksBlake3V6ZkConfig>::from_bytes(proof_bytes)
            .map_err(|e| format!("v6-zk proof decode failed: {e}"))?;
          let re = p
            .to_bytes()
            .map_err(|e| format!("v6-zk proof re-encode failed: {e}"))?;
          if re != proof_bytes {
            return Err("noncanonical or trailing v6-zk proof bytes".into());
          }
          p
        };
        system
          .verify_multiple_claims(&refs, &proof)
          .map_err(|e| format!("v6-zk STARK verification failed: {e:?}"))
      },
    }
  }
}

#[allow(clippy::too_many_arguments)]
fn prove_lowered_plonkish(
  start: Instant,
  compiled: MultiStarkCircuit<Val>,
  definitions: Vec<CircuitInputs<Val>>,
  schema: ClaimSchema,
  merged: Option<&MergedLayout>,
  assignment: Assignment<Val>,
  inner_vk_digest: [u8; 32],
  claim_digest: [u8; 32],
  mode: ShrinkMode,
  params: OuterFriParams,
  options: PlonkishOptions,
  hops: u8,
  device: Option<i32>,
) -> Result<(PlonkishShrinkOutput, PlonkishCircuitVerifier), String> {
  let trace_dimensions: Vec<(usize, usize)> = definitions
    .iter()
    .map(|d| (d.preprocessed.as_ref().map_or(0, Matrix::height), d.main_width))
    .collect();
  let publics = assignment.public_values().to_vec();
  let claims = schema.materialize(&publics)?;
  let (mut outer, sys_vk_digest, prep_roots, rw, mld) =
    OuterSystem::build(definitions, mode, params, device, true)?;
  let vk_digest = compute_plonkish_vk_digest(
    mode,
    params,
    options.compact_encoding,
    hops,
    usize::from(rw),
    usize::from(mld),
    &sys_vk_digest,
    prep_roots.as_deref(),
    &schema,
  )?;

  let (proof_bytes, breakdown) = outer.prove_and_drop_key(
    compiled,
    assignment,
    merged,
    &claims,
    options.compact_encoding,
  )?;
  let prove_ms = start.elapsed().as_secs_f64() * 1000.0;

  let proof_len = u64::try_from(proof_bytes.len())
    .map_err(|err| format!("proof_len exceeds u64: {err}"))?;
  let envelope = PlonkishEnvelope {
    header: PlonkishHeader {
      mode,
      params,
      compact_encoding: options.compact_encoding,
      hops,
      zk_randomizer_width: rw,
      min_log_degree: mld,
      shrinker_vk_digest: vk_digest,
      inner_vk_digest,
      claim_digest,
      proof_len,
    },
    proof_bytes,
  };
  let envelope_bytes = envelope.to_bytes()?;

  let verifier = PlonkishCircuitVerifier {
    mode,
    params,
    compact_encoding: options.compact_encoding,
    hops,
    vk_digest,
    schema,
    outer,
  };

  let v_start = Instant::now();
  let report = verifier.verify_report(
    &envelope_bytes,
    &publics,
    &inner_vk_digest,
    &claim_digest,
  )?;
  let verify_ms = v_start.elapsed().as_secs_f64() * 1000.0;

  Ok((
    PlonkishShrinkOutput {
      envelope_bytes,
      report,
      breakdown,
      prove_ms,
      verify_ms,
      trace_dimensions,
      vk_digest,
    },
    verifier,
  ))
}

/// Prove a single Plonkish `Circuit<Val>` + `Assignment<Val>` directly into an
/// independently self-verified `IXSTARK6\0` v2 envelope (`--stark-128` or
/// `--stark-128-zk`), also returning the independent verifier handle.
#[allow(clippy::too_many_arguments)]
pub fn prove_plonkish_circuit(
  circuit: Circuit<Val>,
  assignment: Assignment<Val>,
  inner_vk_digest: [u8; 32],
  claim_digest: [u8; 32],
  mode: ShrinkMode,
  params: OuterFriParams,
  options: PlonkishOptions,
  hops: u8,
  device: Option<i32>,
) -> Result<(PlonkishShrinkOutput, PlonkishCircuitVerifier), String> {
  let start = Instant::now();
  let (compiled, definitions, schema, merged) =
    lower_circuit_for_mode(circuit, options, mode, params)?;
  prove_lowered_plonkish(
    start,
    compiled,
    definitions,
    schema,
    merged.as_ref(),
    assignment,
    inner_vk_digest,
    claim_digest,
    mode,
    params,
    options,
    hops,
    device,
  )
}

/// Independent verifier for a Plonkish-shrunk `IXSTARK6\0` v2 envelope.
pub struct PlonkishCircuitVerifier {
  mode: ShrinkMode,
  params: OuterFriParams,
  compact_encoding: bool,
  hops: u8,
  vk_digest: [u8; 32],
  schema: ClaimSchema,
  outer: OuterSystem,
}

impl PlonkishCircuitVerifier {
  fn from_lowered(
    definitions: Vec<CircuitInputs<Val>>,
    schema: ClaimSchema,
    mode: ShrinkMode,
    params: OuterFriParams,
    options: PlonkishOptions,
    hops: u8,
  ) -> Result<Self, String> {
    let (outer, sys_vk_digest, prep_roots, rw, mld) =
      OuterSystem::build(definitions, mode, params, None, false)?;
    let vk_digest = compute_plonkish_vk_digest(
      mode,
      params,
      options.compact_encoding,
      hops,
      usize::from(rw),
      usize::from(mld),
      &sys_vk_digest,
      prep_roots.as_deref(),
      &schema,
    )?;
    Ok(Self {
      mode,
      params,
      compact_encoding: options.compact_encoding,
      hops,
      vk_digest,
      schema,
      outer,
    })
  }

  /// Derive the verifier independently from the circuit description alone
  /// (without any proof or witness).
  pub fn derive(
    circuit: Circuit<Val>,
    mode: ShrinkMode,
    params: OuterFriParams,
    options: PlonkishOptions,
    hops: u8,
  ) -> Result<Self, String> {
    let (_compiled, definitions, schema, _merged) =
      lower_circuit_for_mode(circuit, options, mode, params)?;
    Self::from_lowered(definitions, schema, mode, params, options, hops)
  }

  /// Derive an independent Plonkish verifier for a normalized `FixedRoot`
  /// aggregate backend without any proof or witness.
  ///
  /// Uses the exact same deterministic hop planner as [`shrink_fixed_root`]:
  /// 1 hop when the `FixedRoot` verifier fits directly inside `max_trace_height`,
  /// or automatic multi-hop lowering (up to [`MAX_PLONKISH_HOPS`]) for large
  /// multi-circuit `FixedRoot`s.
  pub fn derive_fixed_root(
    inner_key: &AiurVerifyingKey,
    layout: &FixedRoot,
    mode: ShrinkMode,
    params: OuterFriParams,
    options: PlonkishOptions,
  ) -> Result<Self, String> {
    let mut circuit = layout
      .circuit(inner_key, VerifierLimits::default())
      .map_err(|e| format!("fixed root verifier circuit failed: {e}"))?;
    for hop in 1..=MAX_PLONKISH_HOPS {
      match plan_hop_lowering(circuit, options, mode, params, hop)? {
        HopLowering::Final { definitions, schema, .. } => {
          check_endpoint1_outer_layout(&definitions, params)?;
          return Self::from_lowered(
            definitions,
            schema,
            mode,
            params,
            options,
            hop,
          );
        },
        HopLowering::Intermediate {
          compiled,
          definitions,
          schema,
          hop_params,
          ..
        } => {
          drop(compiled);
          hop_params.check_for_mode(ShrinkMode::Stark128, None)?;
          let config = GoldilocksBlake3V6Config::with_device(
            hop_params.commitment(),
            hop_params.fri(),
            FriBatching::Tensor,
            None,
          );
          let (sys, key) =
            System::new_without_preprocessed(config, definitions);
          drop(key);
          #[cfg(feature = "cuda")]
          multi_stark::cuda::release_device_memory();
          let hop_vk = VerifierKey::new(sys);
          let (plan, stmt_schema, _profile) =
            next_hop_verifier_plan(&hop_vk, &schema)?;
          let (next_circuit, _inputs) = plan
            .build(
              stmt_schema,
              ImplementationOptions { compact_blake3: options.compact_blake3 },
            )
            .map_err(|e| {
              format!("hop {} circuit build failed: {e}", hop + 1)
            })?;
          circuit = next_circuit;
        },
      }
    }
    Err(format!(
      "FixedRoot verifier derivation exceeded {MAX_PLONKISH_HOPS} hops"
    ))
  }

  pub const fn vk_digest(&self) -> &[u8; 32] {
    &self.vk_digest
  }

  pub const fn hops(&self) -> u8 {
    self.hops
  }

  pub fn num_outer_circuits(&self) -> usize {
    self.outer.num_circuits()
  }

  pub fn verify(
    &self,
    envelope_bytes: &[u8],
    expected_publics: &[Val],
    expected_inner_vk_digest: &[u8; 32],
    expected_claim_digest: &[u8; 32],
  ) -> Result<PlonkishHeader, String> {
    Ok(
      self
        .verify_report(
          envelope_bytes,
          expected_publics,
          expected_inner_vk_digest,
          expected_claim_digest,
        )?
        .header,
    )
  }

  /// Verify an envelope against this verifier's derived outer system, the
  /// caller's public values, inner-key digest and claim digest (all
  /// mandatory).
  pub fn verify_report(
    &self,
    envelope_bytes: &[u8],
    expected_publics: &[Val],
    expected_inner_vk_digest: &[u8; 32],
    expected_claim_digest: &[u8; 32],
  ) -> Result<PlonkishVerifyReport, String> {
    let start = Instant::now();
    let envelope = PlonkishEnvelope::from_bytes(envelope_bytes)?;
    let h = envelope.header;
    if h.mode != self.mode {
      return Err(format!(
        "shrink mode mismatch (cross-mode replay rejected): verifier expects {} but envelope is {}",
        self.mode.cli_flag(),
        h.mode.cli_flag()
      ));
    }
    if h.params != self.params {
      return Err(format!(
        "outer FRI params mismatch: verifier expects {:?}, envelope has {:?}",
        self.params, h.params
      ));
    }
    if h.compact_encoding != self.compact_encoding || h.hops != self.hops {
      return Err("envelope encoding/hops mismatch with verifier".into());
    }
    if h.shrinker_vk_digest != self.vk_digest {
      return Err("shrinker VK digest mismatch".into());
    }
    if &h.inner_vk_digest != expected_inner_vk_digest {
      return Err("inner VK digest mismatch".into());
    }
    if &h.claim_digest != expected_claim_digest {
      return Err("claim digest mismatch".into());
    }
    if &hash_publics(expected_publics) != expected_claim_digest {
      return Err(
        "expected claim digest is not the digest of the expected public values"
          .into(),
      );
    }
    let claims = self.schema.materialize(expected_publics)?;
    self.outer.verify_bytes(
      &claims,
      &envelope.proof_bytes,
      h.compact_encoding,
    )?;
    let verify_ms = start.elapsed().as_secs_f64() * 1000.0;
    Ok(PlonkishVerifyReport::build(
      h,
      envelope_bytes.len(),
      verify_ms,
      self.outer.num_circuits(),
    ))
  }
}

/// Plonkish shrinker for a normalized Protocol `v6` aggregate root with a
/// trusted [`FixedRoot`] layout (`.ixl`).
///
/// Uses 1 direct hop whenever the verifier circuit fits inside
/// `options.max_trace_height`, and automatically lowers through transparent
/// in-circuit-verifiable intermediate hops (up to [`MAX_PLONKISH_HOPS`]) when
/// a full-scale multi-circuit `FixedRoot` exceeds `max_trace_height` (such as
/// a 59-circuit Release `0.5` aggregate root).
///
/// The hop schedule depends solely on `(inner_key, layout, mode, params, options)`
/// — never on any proof or witness — so [`PlonkishCircuitVerifier::derive_fixed_root`]
/// derives the exact same pinned `shrinker_vk_digest` and `hops` independently.
#[allow(clippy::too_many_arguments)]
pub fn shrink_fixed_root(
  inner_key: &AiurVerifyingKey,
  layout: &FixedRoot,
  inner_proof: &AiurBatchProof,
  expected_claim: &[Val],
  mode: ShrinkMode,
  params: OuterFriParams,
  options: PlonkishOptions,
  device: Option<i32>,
) -> Result<(PlonkishShrinkOutput, PlonkishCircuitVerifier), String> {
  let start = Instant::now();
  let prepared = layout
    .prepare(inner_key, inner_proof, expected_claim, VerifierLimits::default())
    .map_err(|e| format!("fixed root preparation failed: {e}"))?;
  let (mut circuit, mut assignment) = prepared.into_parts();
  let inner_vk_digest = layout.identity(inner_key);
  let claim_digest = hash_publics(expected_claim);

  for hop in 1..=MAX_PLONKISH_HOPS {
    match plan_hop_lowering(circuit, options, mode, params, hop)? {
      HopLowering::Final { compiled, definitions, schema, merged } => {
        check_endpoint1_outer_layout(&definitions, params)?;
        return prove_lowered_plonkish(
          start,
          compiled,
          definitions,
          schema,
          merged.as_ref(),
          assignment,
          inner_vk_digest,
          claim_digest,
          mode,
          params,
          options,
          hop,
          device,
        );
      },
      HopLowering::Intermediate {
        compiled,
        definitions,
        schema,
        merged,
        hop_params,
      } => {
        let (next_circuit, next_assignment) = prove_intermediate_hop(
          compiled,
          definitions,
          &schema,
          merged.as_ref(),
          assignment,
          expected_claim,
          hop_params,
          options,
          hop,
          device,
        )?;
        circuit = next_circuit;
        assignment = next_assignment;
      },
    }
  }
  Err(format!("FixedRoot shrinking exceeded {MAX_PLONKISH_HOPS} hops"))
}

/// Strict 1-hop Plonkish shrinker for a normalized Protocol `v6` aggregate root
/// with a trusted [`FixedRoot`] layout (`.ixl`).
#[allow(clippy::too_many_arguments)]
pub fn shrink_fixed_root_1hop(
  inner_key: &AiurVerifyingKey,
  layout: &FixedRoot,
  inner_proof: &AiurBatchProof,
  expected_claim: &[Val],
  mode: ShrinkMode,
  params: OuterFriParams,
  options: PlonkishOptions,
  device: Option<i32>,
) -> Result<(PlonkishShrinkOutput, PlonkishCircuitVerifier), String> {
  let prepared = layout
    .prepare(inner_key, inner_proof, expected_claim, VerifierLimits::default())
    .map_err(|e| format!("fixed root preparation failed: {e}"))?;
  let (circuit, assignment) = prepared.into_parts();
  let inner_vk_digest = layout.identity(inner_key);
  let claim_digest = hash_publics(expected_claim);
  prove_plonkish_circuit(
    circuit,
    assignment,
    inner_vk_digest,
    claim_digest,
    mode,
    params,
    options,
    1,
    device,
  )
}

/// 1-hop Plonkish shrinker for a fixed-profile Protocol `v6` inner `BatchProof`.
pub fn shrink_single_batch_1hop(
  inner_key: &VerifierKey,
  profile: ProofProfile,
  schema: Statement<StatementSlot>,
  inner_proof: &BatchProof<GoldilocksBlake3V6Config>,
  statement: &Statement<Val>,
  mode: ShrinkMode,
  params: OuterFriParams,
  options: PlonkishOptions,
  device: Option<i32>,
) -> Result<(PlonkishShrinkOutput, PlonkishCircuitVerifier), String> {
  let plan =
    VerifierPlan::validate(inner_key, profile, VerifierLimits::default())
      .map_err(|e| format!("inner plan invalid: {e}"))?;
  let impl_opts =
    ImplementationOptions { compact_blake3: options.compact_blake3 };
  let (circuit, inputs) = plan
    .build(schema, impl_opts)
    .map_err(|e| format!("plonkish verifier build failed: {e}"))?;
  let expanded = plan
    .expand_witness(ProofEnvelope::SingleBatch(inner_proof))
    .map_err(|e| format!("inner witness expansion failed: {e}"))?;
  let mut witness = circuit.witness();
  inputs
    .assign_statement(&mut witness, statement)
    .map_err(|e| format!("statement assignment failed: {e}"))?;
  expanded
    .assign_proof(&mut witness, &inputs)
    .map_err(|e| format!("proof assignment failed: {e}"))?;
  let assignment = witness
    .generate()
    .map_err(|e| format!("witness generation failed: {e}"))?;

  let inner_vk_digest = inner_key
    .fingerprint()
    .map_err(|e| format!("inner vk fingerprint failed: {e}"))?;
  let claim_digest = hash_publics(assignment.public_values());
  prove_plonkish_circuit(
    circuit,
    assignment,
    inner_vk_digest,
    claim_digest,
    mode,
    params,
    options,
    1,
    device,
  )
}

/// 2-hop Plonkish shrinker:
/// - Hop 1: fast transparent Protocol `v6` (`cap=0, mla=1, lfp=0`) verifying the
///   inner `BatchProof` with `compact_blake3 = true`.
/// - Hop 2: verifies Hop 1 (`Envelope::Ordinary`) and proves with `mode`
///   (`--stark-128` or `--stark-128-zk`) under `hop2_params` and `hop2_options`
///   (e.g., `compact_blake3 = false` for a 2-trace ultra-compact proof!).
#[allow(clippy::too_many_arguments)]
pub fn shrink_single_batch_2hop(
  inner_key: &VerifierKey,
  profile: ProofProfile,
  schema: Statement<StatementSlot>,
  inner_proof: &BatchProof<GoldilocksBlake3V6Config>,
  statement: &Statement<Val>,
  hop1_params: OuterFriParams,
  hop1_options: PlonkishOptions,
  hop2_mode: ShrinkMode,
  hop2_params: OuterFriParams,
  hop2_options: PlonkishOptions,
  device: Option<i32>,
) -> Result<(PlonkishShrinkOutput, PlonkishCircuitVerifier, f64, usize), String>
{
  if hop1_params.cap_height != 0
    || hop1_params.max_log_arity != 1
    || hop1_params.log_final_poly_len != 0
  {
    return Err(
      "Hop 1 must use cap_height=0, max_log_arity=1, log_final_poly_len=0 for in-circuit Hop-2 verification".into(),
    );
  }
  hop1_params.check()?;
  let hop1_start = Instant::now();

  // --- Hop 1: prove inner BatchProof into transparent v6 multi-stark Proof ---
  let plan1 =
    VerifierPlan::validate(inner_key, profile, VerifierLimits::default())
      .map_err(|e| format!("hop1 inner plan invalid: {e}"))?;
  let (circuit1, inputs1) = plan1
    .build(
      schema,
      ImplementationOptions { compact_blake3: hop1_options.compact_blake3 },
    )
    .map_err(|e| format!("hop1 verifier build failed: {e}"))?;
  let expanded1 = plan1
    .expand_witness(ProofEnvelope::SingleBatch(inner_proof))
    .map_err(|e| format!("hop1 witness expansion failed: {e}"))?;
  let mut witness1 = circuit1.witness();
  inputs1
    .assign_statement(&mut witness1, statement)
    .map_err(|e| format!("hop1 statement assign failed: {e}"))?;
  expanded1
    .assign_proof(&mut witness1, &inputs1)
    .map_err(|e| format!("hop1 proof assign failed: {e}"))?;
  let assignment1 = witness1
    .generate()
    .map_err(|e| format!("hop1 witness generation failed: {e}"))?;
  let publics1 = assignment1.public_values().to_vec();

  let (compiled1, defs1, claim_schema1, merged1) = lower_circuit_for_mode(
    circuit1,
    hop1_options,
    ShrinkMode::Stark128,
    hop1_params,
  )?;
  let claims1 = claim_schema1.materialize(&publics1)?;
  let config1 = GoldilocksBlake3V6Config::with_device(
    hop1_params.commitment(),
    hop1_params.fri(),
    FriBatching::Tensor,
    device,
  );
  let (sys1, key1) = System::new_without_preprocessed(config1, defs1);
  let stage1 = if let Some(layout) = merged1.as_ref()
    && layout.is_merged()
  {
    let traces = layout.build_traces(&compiled1, &assignment1)?;
    sys1.prove_stage_1_streaming(traces)
  } else {
    let shards1 = compiled1
      .trace_shards(&assignment1)
      .map_err(|e| format!("hop1 trace shards failed: {e}"))?;
    let count1 = sys1.circuits.len();
    let mut trace_err1: Option<String> = None;
    let s1 =
      sys1.prove_stage_1_streaming((0..count1).map(
        |ci| match shards1.trace(ci) {
          Ok(t) => t,
          Err(e) => {
            if trace_err1.is_none() {
              trace_err1 = Some(format!("hop1 trace {ci}: {e}"));
            }
            RowMajorMatrix::new(Vec::new(), sys1.circuits[ci].main_width)
          },
        },
      ));
    if let Some(err) = trace_err1 {
      return Err(err);
    }
    s1
  };
  drop(compiled1);
  drop(assignment1);
  let refs1: Vec<&[Val]> = claims1.iter().map(Vec::as_slice).collect();
  let hop1_proof = sys1.prove_committed(&key1, &refs1, stage1);
  drop(key1);
  #[cfg(feature = "cuda")]
  multi_stark::cuda::release_device_memory();
  sys1
    .verify_multiple_claims(&refs1, &hop1_proof)
    .map_err(|e| format!("hop1 self-verify failed: {e:?}"))?;
  let hop1_bytes = hop1_proof
    .to_bytes()
    .map_err(|e| format!("hop1 serialize failed: {e}"))?
    .len();
  let hop1_ms = hop1_start.elapsed().as_secs_f64() * 1000.0;

  // --- Hop 2: build Plonkish verifier for Hop 1 and prove in `hop2_mode` ---
  let hop1_vk = VerifierKey::new(sys1);
  let hop1_log_degrees: Vec<u8> = hop1_vk
    .system()
    .circuits
    .iter()
    .map(|c| {
      u8::try_from(c.preprocessed_height.ilog2())
        .map_err(|err| format!("hop1 log_degree overflow: {err}"))
    })
    .collect::<Result<_, _>>()?;
  let hop2_profile = ProofProfile {
    envelope: FriEnvelope::Ordinary,
    active: vec![true; hop1_vk.system().circuits.len()],
    log_degrees: hop1_log_degrees,
    claim_lengths: claims1.iter().map(Vec::len).collect(),
    message_lengths: vec![],
    max_field_retries: ix_proof_compression::fri::DEFAULT_FIELD_RETRIES,
  };
  let mut hop2_stmt_schema = Statement {
    claims: claim_schema1
      .template
      .iter()
      .map(|row| row.iter().copied().map(StatementSlot::Constant).collect())
      .collect(),
    messages: vec![],
  };
  for &(r, c) in &claim_schema1.locations {
    hop2_stmt_schema.claims[r][c] = StatementSlot::Public;
  }

  let plan2 =
    VerifierPlan::validate(&hop1_vk, hop2_profile, VerifierLimits::default())
      .map_err(|e| format!("hop2 plan invalid: {e}"))?;
  let (circuit2, inputs2) = plan2
    .build(
      hop2_stmt_schema,
      ImplementationOptions { compact_blake3: hop2_options.compact_blake3 },
    )
    .map_err(|e| format!("hop2 circuit build failed: {e}"))?;
  let expanded2 = plan2
    .expand_witness(ProofEnvelope::Ordinary {
      proof: &hop1_proof,
      claims: &claims1,
    })
    .map_err(|e| format!("hop2 witness expansion failed: {e}"))?;
  let mut witness2 = circuit2.witness();
  inputs2
    .assign_statement(
      &mut witness2,
      &Statement { claims: claims1, messages: vec![] },
    )
    .map_err(|e| format!("hop2 statement assign failed: {e}"))?;
  expanded2
    .assign_proof(&mut witness2, &inputs2)
    .map_err(|e| format!("hop2 proof assign failed: {e}"))?;
  let assignment2 = witness2
    .generate()
    .map_err(|e| format!("hop2 witness generate failed: {e}"))?;

  let inner_vk_digest = inner_key
    .fingerprint()
    .map_err(|e| format!("inner vk fingerprint failed: {e}"))?;
  let claim_digest = hash_publics(&publics1);

  let (out2, ver2) = prove_plonkish_circuit(
    circuit2,
    assignment2,
    inner_vk_digest,
    claim_digest,
    hop2_mode,
    hop2_params,
    hop2_options,
    2,
    device,
  )?;
  Ok((out2, ver2, hop1_ms, hop1_bytes))
}

/// Canonical BLAKE3 digest of a Plonkish public-input vector (`len || words`, LE u64).
pub fn hash_publics(publics: &[Val]) -> [u8; 32] {
  let mut h = blake3::Hasher::new();
  h.update(&(publics.len() as u64).to_le_bytes());
  for &v in publics {
    h.update(&v.as_canonical_u64().to_le_bytes());
  }
  *h.finalize().as_bytes()
}

/// Strictly decode a single serialized batch claim produced by
/// `MultiStark.serializeClaims #[claim]` (length-prefixed list of 1 claim of
/// little-endian canonical Goldilocks `u64` words, with zero trailing bytes).
pub fn decode_single_claim_bytes(bytes: &[u8]) -> Result<Vec<Val>, String> {
  let (words, remainder) = bytes.as_chunks::<8>();
  if !remainder.is_empty() || words.len() < 2 {
    return Err(format!(
      "serialized statement must be a multiple of 8 bytes with at least 2 header words (got {} bytes)",
      bytes.len()
    ));
  }
  let count = u64::from_le_bytes(words[0]);
  if count != 1 {
    return Err(format!(
      "FixedRoot statement must contain exactly 1 claim (got {count})"
    ));
  }
  let claim_len_u64 = u64::from_le_bytes(words[1]);
  let claim_len = usize::try_from(claim_len_u64)
    .map_err(|err| format!("statement claim length overflows usize: {err}"))?;
  if claim_len == 0 {
    return Err("FixedRoot statement claim must not be empty".into());
  }
  let expected_words =
    claim_len.checked_add(2).ok_or("statement word count overflow")?;
  if words.len() != expected_words {
    return Err(format!(
      "serialized statement length mismatch: header declares {claim_len} words ({expected_words} total), got {} words",
      words.len()
    ));
  }
  let mut claim = Vec::with_capacity(claim_len);
  for (idx, chunk) in words[2..].iter().enumerate() {
    let raw = u64::from_le_bytes(*chunk);
    if raw >= Val::ORDER_U64 {
      return Err(format!(
        "statement word {idx} ({raw}) is not a canonical Goldilocks field element"
      ));
    }
    claim.push(Val::from_u64(raw));
  }
  Ok(claim)
}

#[cfg(test)]
mod tests {
  use super::*;
  use aiur::trace::stark::Parameters;
  use multi_stark::{
    batch::ShardInput, expr::Expr, lookup::Lookup, system::SystemWitness,
  };

  /// Build a production-grade Protocol `v6` (`lb=2, q=128, qpow=20`, 142.24b Johnson)
  /// multi-circuit inner `BatchProof` with `num_circuits` circuits (including a
  /// preprocessed lookup table so `ix_proof_compression::fri` verifies it).
  fn build_inner_v6_batch(
    num_extra_circuits: usize,
    log_height: u8,
  ) -> (
    VerifierKey,
    ProofProfile,
    Statement<StatementSlot>,
    Statement<Val>,
    BatchProof<GoldilocksBlake3V6Config>,
  ) {
    let params = Parameters::DEFAULT; // lb=2, q=128, qpow=20 (142.24b Johnson)
    let (cp, fp) = (params.commitment(), params.fri());
    let height = 1usize << log_height;

    let mut inputs = Vec::with_capacity(num_extra_circuits + 2);
    let mut traces = Vec::with_capacity(num_extra_circuits + 2);

    // Circuit 0: square-and-lookup circuit exposing 18-word claim (matching ix_aggr).
    let x = Expr::main(0);
    let y = Expr::main(1);
    let sel = Expr::preprocessed(0);
    let one = Expr::constant(Val::ONE);
    let mut prep0 = vec![Val::ZERO; height];
    prep0[0] = Val::ONE;
    inputs.push(CircuitInputs {
      main_width: 4,
      preprocessed: Some(RowMajorMatrix::new_col(prep0)),
      constraints: vec![x.clone() * x.clone() - y.clone()],
      lookups: vec![
        Lookup::pull(
          sel.clone(),
          vec![one.clone(), Expr::constant(Val::ZERO), x.clone(), y.clone()],
        ),
        Lookup::pull(one.clone(), vec![Expr::constant(Val::from_u64(99)), x]),
      ],
      ..Default::default()
    });
    let mut t0 = vec![Val::ZERO; 4 * height];
    for r in 0..height {
      let v = Val::from_u64((r as u64 % 16) + 1);
      t0[4 * r] = v;
      t0[4 * r + 1] = v * v;
    }
    t0[0] = Val::from_u64(3);
    t0[1] = Val::from_u64(9);
    traces.push(RowMajorMatrix::new(t0, 4));

    // Extra circuits simulating a multi-circuit Aiur/ix_aggr system.
    for ci in 0..num_extra_circuits {
      let a = Expr::main(0);
      let b = Expr::main(1);
      let c = Expr::main(2);
      inputs.push(CircuitInputs {
        main_width: 8,
        constraints: vec![a.clone() * b.clone() - c],
        lookups: vec![Lookup::pull(
          Expr::constant(Val::ONE),
          vec![Expr::constant(Val::from_u64(99)), a],
        )],
        ..Default::default()
      });
      let mut tr = vec![Val::ZERO; 8 * height];
      for r in 0..height {
        let va = Val::from_u64(((r + ci) as u64 % 16) + 1);
        let vb = Val::from_u64(5);
        tr[8 * r] = va;
        tr[8 * r + 1] = vb;
        tr[8 * r + 2] = va * vb;
      }
      traces.push(RowMajorMatrix::new(tr, 8));
    }

    // Final circuit: fixed lookup table for values 1..=16 (height 256).
    let tbl_h = 256usize;
    let tbl_prep: Vec<Val> =
      (0..tbl_h).map(|i| Val::from_u64((i as u64 % 16) + 1)).collect();
    inputs.push(CircuitInputs {
      main_width: 1,
      preprocessed: Some(RowMajorMatrix::new_col(tbl_prep)),
      lookups: vec![Lookup::push(
        Expr::main(0),
        vec![Expr::constant(Val::from_u64(99)), Expr::preprocessed(0)],
      )],
      ..Default::default()
    });
    let mut mults = vec![0u64; tbl_h];
    // Circuit 0 pulls (r % 16) + 1 for r in 1..height, and value 3 at r=0.
    mults[2] += 1; // value 3 is at index 2
    for r in 1..height {
      mults[r % 16] += 1;
    }
    for ci in 0..num_extra_circuits {
      for r in 0..height {
        mults[(r + ci) % 16] += 1;
      }
    }
    let t_tbl: Vec<Val> = mults.into_iter().map(Val::from_u64).collect();
    traces.push(RowMajorMatrix::new_col(t_tbl));

    let (system, pk) =
      System::new(GoldilocksBlake3V6Config::new(cp, fp), inputs);
    let claims =
      vec![vec![Val::ONE, Val::ZERO, Val::from_u64(3), Val::from_u64(9)]];
    let witness = SystemWitness::from_stage_1(traces, &system);
    let proof = system.prove_batch(
      &pk,
      vec![ShardInput { claims: claims.clone(), witness }],
      vec![],
    );
    system.verify_batch(&proof).expect("inner v6 batch verifies");

    let n_circuits = system.circuits.len();
    let mut log_degrees = vec![log_height; n_circuits - 1];
    log_degrees.push(8);
    let profile = ProofProfile {
      envelope: FriEnvelope::SingleBatch,
      active: vec![true; n_circuits],
      log_degrees,
      claim_lengths: vec![4],
      message_lengths: vec![],
      max_field_retries: ix_proof_compression::fri::DEFAULT_FIELD_RETRIES,
    };
    let schema = Statement {
      claims: vec![vec![StatementSlot::Public; 4]],
      messages: vec![],
    };
    let statement = Statement { claims, messages: vec![] };
    let vk = VerifierKey::from_system(&system);
    (vk, profile, schema, statement, proof)
  }

  fn peak_rss_mib() -> f64 {
    std::fs::read_to_string("/proc/self/status")
      .ok()
      .and_then(|s| {
        s.lines()
          .find(|l| l.starts_with("VmHWM:"))
          .and_then(|l| l.split_whitespace().nth(1))
          .and_then(|v| v.parse::<f64>().ok())
          .map(|kb| kb / 1024.0)
      })
      .unwrap_or(0.0)
  }

  #[allow(clippy::cast_precision_loss)]
  fn to_kib(bytes: usize) -> f64 {
    bytes as f64 / 1024.0
  }

  /// Serialize concurrent CUDA tests onto the GPU so multi-million-row provers
  /// do not contend for the same device's VRAM under `cargo test`.
  #[cfg(feature = "cuda")]
  fn gpu_test_guard() -> std::sync::MutexGuard<'static, ()> {
    static GPU_LOCK: std::sync::Mutex<()> = std::sync::Mutex::new(());
    GPU_LOCK.lock().unwrap_or_else(std::sync::PoisonError::into_inner)
  }

  fn dummy_plonkish_envelope(
    mode: ShrinkMode,
    params: OuterFriParams,
  ) -> Vec<u8> {
    let rw = u16::try_from(mode.expected_randomizer_width()).unwrap();
    let mld =
      u16::try_from(mode.expected_min_log_degree(params.num_queries)).unwrap();
    PlonkishEnvelope {
      header: PlonkishHeader {
        mode,
        params,
        compact_encoding: true,
        hops: 1,
        zk_randomizer_width: rw,
        min_log_degree: mld,
        shrinker_vk_digest: [0x11; 32],
        inner_vk_digest: [0x22; 32],
        claim_digest: [0x33; 32],
        proof_len: 4,
      },
      proof_bytes: vec![1, 2, 3, 4],
    }
    .to_bytes()
    .unwrap()
  }

  #[test]
  fn plonkish_envelope_fail_closed_security_controls() {
    let params = OuterFriParams::COMPACT_400KB_FAST;
    for mode in [ShrinkMode::Stark128, ShrinkMode::Stark128Zk] {
      let good = dummy_plonkish_envelope(mode, params);
      let parsed = PlonkishEnvelope::from_bytes(&good).unwrap();
      assert_eq!(parsed.header.mode, mode);
      assert_eq!(parsed.header.params, params);
      assert_eq!(parsed.to_bytes().unwrap(), good);
      assert_eq!(peek_plonkish_header(&good).unwrap(), parsed.header);

      // Bad magic
      let mut bad = good.clone();
      bad[7] = b'5';
      assert!(peek_plonkish_header(&bad).is_err());

      // Bad envelope version (v1 Aiur or v3 unknown)
      for v in [1u16, 3u16] {
        let mut bad = good.clone();
        bad[9..11].copy_from_slice(&v.to_le_bytes());
        assert!(peek_plonkish_header(&bad).is_err());
      }

      // Protocol v5 downgrade rejected fail-closed
      let mut bad = good.clone();
      bad[11..13].copy_from_slice(&5u16.to_le_bytes());
      assert!(peek_plonkish_header(&bad).unwrap_err().contains("retired"));

      // Fp^2 downgrade rejected fail-closed
      let mut bad = good.clone();
      bad[13..15].copy_from_slice(&2u16.to_le_bytes());
      assert!(peek_plonkish_header(&bad).unwrap_err().contains("Fp^2"));

      // Unknown mode tag rejected
      let mut bad = good.clone();
      bad[15] = 9;
      assert!(peek_plonkish_header(&bad).is_err());

      // Horner batching downgrade rejected fail-closed
      let mut bad = good.clone();
      bad[16] = 0;
      assert!(peek_plonkish_header(&bad).unwrap_err().contains("Tensor"));

      // Invalid payload codec tag rejected
      let mut bad = good.clone();
      bad[17] = 2;
      assert!(peek_plonkish_header(&bad).is_err());

      // Invalid hop count rejected
      for hops in [0u8, MAX_PLONKISH_HOPS + 1] {
        let mut bad = good.clone();
        bad[18] = hops;
        assert!(peek_plonkish_header(&bad).is_err());
      }

      // Sub-128-bit FRI queries rejected fail-closed (num_queries at offset 27..29)
      let mut bad = good.clone();
      bad[27..29].copy_from_slice(&40u16.to_le_bytes());
      assert!(peek_plonkish_header(&bad).is_err());

      // lb=4, q=58, qpow=20 (72.9b UD < 80b floor) rejected fail-closed
      let mut bad = good.clone();
      bad[19..21].copy_from_slice(&4u16.to_le_bytes()); // lb=4
      bad[27..29].copy_from_slice(&58u16.to_le_bytes()); // q=58
      bad[31..33].copy_from_slice(&20u16.to_le_bytes()); // qpow=20
      assert!(peek_plonkish_header(&bad).is_err());

      // The shape is checked on the real values (formerly replaced by
      // `cap 0, arity 2, lfp 0` before the floor): Merkle caps, folding by more
      // than 8 and final polynomials above 2^8 are rejected. Offsets: cap
      // 21..23, lfp 23..25, max_log_arity 25..27.
      for (offset, value, needle) in [
        (21, 4u16, "cap_height"),
        (21, 12, "cap_height"),
        (25, 4, "max_log_arity"),
        (25, 0, "max_log_arity"),
        (23, 9, "log_final_poly_len"),
        (23, 12, "log_final_poly_len"),
      ] {
        let mut bad = good.clone();
        bad[offset..offset + 2].copy_from_slice(&value.to_le_bytes());
        let err = peek_plonkish_header(&bad).unwrap_err();
        assert!(err.contains(needle), "{offset}={value}: {err}");
      }
      // Capped / higher-arity shapes that previously slipped past the floor are rejected.
      for shape in [
        (3usize, 75usize, 0usize, 20usize, 4usize, 3usize, 8usize),
        (3, 75, 0, 20, 12, 4, 8),
        (3, 66, 0, 32, 12, 4, 8),
        (1, 282, 0, 0, 12, 4, 0),
        (4, 88, 0, 0, 12, 4, 8),
      ] {
        let (log_blowup, num_queries, cpow, qpow, cap, mla, lfp) = shape;
        let p = OuterFriParams {
          log_blowup,
          num_queries,
          commit_proof_of_work_bits: cpow,
          query_proof_of_work_bits: qpow,
          cap_height: cap,
          max_log_arity: mla,
          log_final_poly_len: lfp,
        };
        assert!(p.check().is_err(), "{shape:?}");
      }

      // Trailing byte rejected
      let mut bad = good.clone();
      bad.push(0);
      assert!(
        peek_plonkish_header(&bad).unwrap_err().contains("length mismatch")
      );

      // Truncated rejected
      let mut bad = good.clone();
      bad.pop();
      assert!(peek_plonkish_header(&bad).is_err());
    }

    // Mode-specific ZK traps:
    // 1. Transparent mode rejects nonzero W_R (offset 33..35)
    let mut bad = dummy_plonkish_envelope(ShrinkMode::Stark128, params);
    bad[33..35].copy_from_slice(&4u16.to_le_bytes());
    assert!(peek_plonkish_header(&bad).is_err());

    // 2. ZK mode rejects W_R < 4
    let mut bad = dummy_plonkish_envelope(ShrinkMode::Stark128Zk, params);
    bad[33..35].copy_from_slice(&3u16.to_le_bytes());
    assert!(
      peek_plonkish_header(&bad).unwrap_err().contains("randomizer width")
    );

    // 3. ZK mode rejects min_log_degree < 8 (offset 35..37)
    let mut bad = dummy_plonkish_envelope(ShrinkMode::Stark128Zk, params);
    bad[35..37].copy_from_slice(&7u16.to_le_bytes());
    assert!(peek_plonkish_header(&bad).unwrap_err().contains("min_log_degree"));

    // 4. ZK mode rejects log_blowup = 2
    let mut bad = dummy_plonkish_envelope(ShrinkMode::Stark128Zk, params);
    bad[19..21].copy_from_slice(&2u16.to_le_bytes()); // lb=2
    bad[27..29].copy_from_slice(&128u16.to_le_bytes()); // q=128
    bad[35..37].copy_from_slice(&9u16.to_le_bytes()); // min_log_degree(128, 3)=9
    assert!(
      peek_plonkish_header(&bad).unwrap_err().contains("log_blowup >= 3")
    );
  }

  /// The Endpoint 1 verifier admits exactly the two shipped presets in
  /// both modes; any other header, including floor-passing ones, is refused.
  #[test]
  fn endpoint1_admits_only_the_shipped_profiles() {
    let header = |mode, params| PlonkishHeader {
      mode,
      params,
      compact_encoding: true,
      hops: 1,
      zk_randomizer_width: 0,
      min_log_degree: 0,
      shrinker_vk_digest: [0; 32],
      inner_vk_digest: [0; 32],
      claim_digest: [0; 32],
      proof_len: 1,
    };
    for mode in [ShrinkMode::Stark128, ShrinkMode::Stark128Zk] {
      for params in [
        OuterFriParams::COMPACT_400KB_BALANCED,
        OuterFriParams::ULTRA_COMPACT_400KB_ZK,
      ] {
        params.check_for_mode(mode, None).unwrap();
        assert_eq!(
          admitted_profile(&header(mode, params), &ENDPOINT1_PROFILES).unwrap(),
          (mode, params)
        );
      }
      for params in [
        OuterFriParams::COMPACT_400KB_FAST,
        OuterFriParams::CUDA_COMPACT_128,
        OuterFriParams::HOP1_DEFAULT,
        OuterFriParams {
          log_blowup: 3,
          num_queries: 75,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 20,
          cap_height: 0,
          max_log_arity: 3,
          log_final_poly_len: 8,
        },
        OuterFriParams {
          num_queries: 53,
          query_proof_of_work_bits: 32,
          ..OuterFriParams::COMPACT_400KB_BALANCED
        },
      ] {
        params.check().unwrap();
        let err = admitted_profile(&header(mode, params), &ENDPOINT1_PROFILES)
          .unwrap_err();
        assert!(err.contains("not an admitted"), "{err}");
      }
    }
  }

  /// The Endpoint 1 outer system must be one circuit whose height
  /// is fixed by its preprocessed matrix and whose LDE reaches the cap layer.
  #[test]
  fn endpoint1_outer_layout_invariant_is_enforced() {
    let fixed = |height: usize| CircuitInputs {
      main_width: 1,
      preprocessed: Some(RowMajorMatrix::new_col(vec![Val::ZERO; height])),
      ..Default::default()
    };
    let params = OuterFriParams::COMPACT_400KB_BALANCED;
    check_endpoint1_outer_layout(&[fixed(1 << 17)], params).unwrap();
    let err = check_endpoint1_outer_layout(&[], params).unwrap_err();
    assert!(err.contains("exactly one circuit"), "{err}");
    let err =
      check_endpoint1_outer_layout(&[fixed(1 << 17), fixed(256)], params)
        .unwrap_err();
    assert!(err.contains("exactly one circuit"), "{err}");
    let unfixed = CircuitInputs::<Val> { main_width: 1, ..Default::default() };
    let err = check_endpoint1_outer_layout(&[unfixed], params).unwrap_err();
    assert!(err.contains("preprocessed"), "{err}");
    // A cap layer above the LDE would leave rows unbound: refused.
    let capped = OuterFriParams { cap_height: 12, log_blowup: 1, ..params };
    let err =
      check_endpoint1_outer_layout(&[fixed(1 << 8)], capped).unwrap_err();
    assert!(err.contains("cap layer"), "{err}");
  }

  #[test]
  fn plonkish_outer_fri_presets_meet_128bit_security_floor() {
    for (name, p) in [
      ("CUDA_COMPACT_128", OuterFriParams::CUDA_COMPACT_128),
      ("COMPACT_400KB_FAST", OuterFriParams::COMPACT_400KB_FAST),
      ("COMPACT_400KB_BALANCED", OuterFriParams::COMPACT_400KB_BALANCED),
      ("ULTRA_COMPACT_400KB_ZK", OuterFriParams::ULTRA_COMPACT_400KB_ZK),
      ("HOP1_DEFAULT", OuterFriParams::HOP1_DEFAULT),
      ("HOP_INTERMEDIATE_FAST", OuterFriParams::HOP_INTERMEDIATE_FAST),
      ("HOP_INTERMEDIATE_COMPACT", OuterFriParams::HOP_INTERMEDIATE_COMPACT),
    ] {
      p.check().unwrap_or_else(|e| panic!("{name} failed floor: {e}"));
      assert!(p.johnson_millibits() >= 128_000, "{name} < 128b Johnson");
      assert!(p.provable_ud_millibits().unwrap() >= 80_000, "{name} < 80b UD");
      assert!(p.conjectured_bits() >= 220, "{name} < 220b conjectured");
      assert_eq!(
        ShrinkMode::Stark128Zk.expected_min_log_degree(p.num_queries),
        min_zk_log_degree(p.num_queries, EXTENSION_DEGREE as usize)
      );
      assert!(
        ShrinkMode::Stark128Zk.expected_min_log_degree(p.num_queries) >= 7
      );
    }
    assert!(OuterFriParams::CUDA_COMPACT_128.is_cuda_compatible());
    assert!(OuterFriParams::COMPACT_400KB_FAST.is_cuda_compatible());
    assert!(OuterFriParams::COMPACT_400KB_BALANCED.is_cuda_compatible());
    assert!(OuterFriParams::ULTRA_COMPACT_400KB_ZK.is_cuda_compatible());
    assert!(OuterFriParams::HOP1_DEFAULT.is_cuda_compatible());
    assert!(OuterFriParams::HOP_INTERMEDIATE_FAST.is_cuda_compatible());
    assert!(OuterFriParams::HOP_INTERMEDIATE_COMPACT.is_cuda_compatible());
    assert!(
      !OuterFriParams {
        cap_height: 1,
        ..OuterFriParams::COMPACT_400KB_BALANCED
      }
      .is_cuda_compatible()
    );
    assert!(
      !OuterFriParams {
        max_log_arity: 0,
        ..OuterFriParams::COMPACT_400KB_BALANCED
      }
      .is_cuda_compatible()
    );
    assert!(
      !OuterFriParams {
        max_log_arity: 5,
        ..OuterFriParams::COMPACT_400KB_BALANCED
      }
      .is_cuda_compatible()
    );
  }

  #[test]
  fn decode_single_claim_bytes_fail_closed() {
    let claim = vec![Val::from_u64(1), Val::from_u64(42), Val::from_u64(99)];
    let bytes = stark_verifier::claims_bytes(std::slice::from_ref(&claim));
    assert_eq!(decode_single_claim_bytes(&bytes).unwrap(), claim);

    // Trailing byte rejected
    let mut bad = bytes.clone();
    bad.push(0);
    assert!(decode_single_claim_bytes(&bad).is_err());

    // Extra word rejected
    let mut bad = bytes.clone();
    bad.extend_from_slice(&0u64.to_le_bytes());
    assert!(decode_single_claim_bytes(&bad).is_err());

    // Truncated rejected
    assert!(decode_single_claim_bytes(&bytes[..bytes.len() - 8]).is_err());
    assert!(decode_single_claim_bytes(&bytes[..8]).is_err());

    // Wrong claim count (0 or 2) rejected
    let mut bad = bytes.clone();
    bad[..8].copy_from_slice(&0u64.to_le_bytes());
    assert!(decode_single_claim_bytes(&bad).is_err());
    let two = stark_verifier::claims_bytes(&[claim.clone(), claim]);
    assert!(decode_single_claim_bytes(&two).is_err());

    // Empty claim rejected
    let empty = stark_verifier::claims_bytes(&[vec![]]);
    assert!(decode_single_claim_bytes(&empty).is_err());

    // Noncanonical Goldilocks field element (>= p) rejected
    let mut noncanon = bytes;
    noncanon[16..24].copy_from_slice(&Val::ORDER_U64.to_le_bytes());
    assert!(decode_single_claim_bytes(&noncanon).is_err());
  }

  /// Build a small Plonkish circuit exercising `ByteGadgets` + compact BLAKE3
  /// so `MergedLayout` triggers the full `B3_All` + 1-lookup `UnifiedTable` +
  /// 1-circuit horizontal packing path in ~1.5–3s.
  fn build_compact_blake3_plonkish_circuit(
    x_val: u64,
  ) -> (Circuit<Val>, Assignment<Val>, Vec<Val>) {
    use ix_proof_compression::fri::{ByteGadgets, blake3_domain};
    use multi_stark::plonkish::CircuitBuilder;

    let build = || {
      let mut b = CircuitBuilder::<Val>::new();
      b.enable_compact_blake3();
      let x = b.public_input("x");
      let y = b.public_input("y");
      let d0 = b.public_input("digest_b0");
      let sq = b.mul(x, x);
      b.assert_equal(sq, y);
      let bytes = ByteGadgets::new(&mut b);
      let enc = bytes.encode_field64(&mut b, x);
      let digest =
        blake3_domain(&mut b, &bytes, Blake3Domain::MerkleLeaf, &enc);
      b.assert_equal(digest[0].value(), d0);
      (b.finish(), [x, y, d0])
    };
    let expected_digest =
      Blake3Domain::MerkleLeaf.hash_bytes(&x_val.to_le_bytes());
    let publics = vec![
      Val::from_u64(x_val),
      Val::from_u64(x_val * x_val),
      Val::from_u64(u64::from(expected_digest[0])),
    ];
    let (circuit, wires) = build();
    let mut witness = circuit.witness();
    for (&w, &v) in wires.iter().zip(&publics) {
      witness.set(w, v).unwrap();
    }
    let assignment = witness.generate().unwrap();
    (circuit, assignment, publics)
  }

  #[test]
  fn plonkish_1circuit_v6_and_v6_zk_roundtrip_tamper_and_cross_mode_replay() {
    #[cfg(feature = "cuda")]
    let _gpu_guard = gpu_test_guard();
    let params = OuterFriParams::COMPACT_400KB_FAST;
    let opts = PlonkishOptions::default();
    let inner_vk_digest = [0xAA; 32];

    let (c_v6, a_v6, publics) = build_compact_blake3_plonkish_circuit(7);
    let claim_digest = hash_publics(&publics);
    let (c_der_v6, _, _) = build_compact_blake3_plonkish_circuit(7);
    let (c_der_zk, _, _) = build_compact_blake3_plonkish_circuit(7);

    // 1. Independently derive verifiers WITHOUT any proof or witness.
    let ver_v6 = PlonkishCircuitVerifier::derive(
      c_der_v6,
      ShrinkMode::Stark128,
      params,
      opts,
      1,
    )
    .unwrap();
    let ver_zk = PlonkishCircuitVerifier::derive(
      c_der_zk,
      ShrinkMode::Stark128Zk,
      params,
      opts,
      1,
    )
    .unwrap();
    assert_eq!(ver_v6.num_outer_circuits(), 1);
    assert_eq!(ver_zk.num_outer_circuits(), 1);
    assert_ne!(
      ver_v6.vk_digest(),
      ver_zk.vk_digest(),
      "v6 and v6-zk Plonkish VK digests must be cryptographically distinct"
    );

    // 2. Roundtrip --stark-128 (transparent v6, 1-circuit, compact codec)
    let (out_v6, _) = prove_plonkish_circuit(
      c_v6,
      a_v6,
      inner_vk_digest,
      claim_digest,
      ShrinkMode::Stark128,
      params,
      opts,
      1,
      None,
    )
    .unwrap();
    assert_eq!(out_v6.vk_digest, *ver_v6.vk_digest());
    assert_eq!(out_v6.trace_dimensions.len(), 1);
    assert_eq!(
      out_v6.breakdown.raw_payload_bytes
        + out_v6.breakdown.bincode_framing_overhead_bytes,
      out_v6.breakdown.total_bincode_bytes
    );
    assert!(
      out_v6.breakdown.total_compact_bytes
        <= out_v6.breakdown.total_bincode_bytes
    );
    assert_eq!(out_v6.breakdown.total_leaf_salts_bytes(), 0);
    let rep_v6 = ver_v6
      .verify_report(
        &out_v6.envelope_bytes,
        &publics,
        &inner_vk_digest,
        &claim_digest,
      )
      .unwrap();
    assert!(rep_v6.banner().contains("NON-ZK"));
    assert!(rep_v6.banner().contains("1 outer circuit(s)"));

    // 3. Roundtrip --stark-128-zk (hiding v6-zk, 1-circuit, compact codec)
    let (c_zk1, a_zk1, _) = build_compact_blake3_plonkish_circuit(7);
    let (out_zk1, _) = prove_plonkish_circuit(
      c_zk1,
      a_zk1,
      inner_vk_digest,
      claim_digest,
      ShrinkMode::Stark128Zk,
      params,
      opts,
      1,
      None,
    )
    .unwrap();
    assert_eq!(out_zk1.vk_digest, *ver_zk.vk_digest());
    assert_eq!(out_zk1.trace_dimensions.len(), 1);
    assert!(out_zk1.breakdown.total_leaf_salts_bytes() > 0);
    let rep_zk = ver_zk
      .verify_report(
        &out_zk1.envelope_bytes,
        &publics,
        &inner_vk_digest,
        &claim_digest,
      )
      .unwrap();
    assert!(rep_zk.banner().contains("BLINDED"));
    assert!(!rep_zk.banner().contains("Post-quantum ready"));
    assert!(rep_zk.banner().contains("W_R=4"));

    // 4. v6-zk fresh randomization: second proof on same witness differs!
    let (c_zk2, a_zk2, _) = build_compact_blake3_plonkish_circuit(7);
    let (out_zk2, _) = prove_plonkish_circuit(
      c_zk2,
      a_zk2,
      inner_vk_digest,
      claim_digest,
      ShrinkMode::Stark128Zk,
      params,
      opts,
      1,
      None,
    )
    .unwrap();
    assert_ne!(
      out_zk1.envelope_bytes, out_zk2.envelope_bytes,
      "v6-zk proofs must be freshly randomized"
    );
    ver_zk
      .verify(
        &out_zk2.envelope_bytes,
        &publics,
        &inner_vk_digest,
        &claim_digest,
      )
      .unwrap();

    // 5. Negative controls across BOTH modes:
    for (label, env_bytes, ver) in [
      ("--stark-128", &out_v6.envelope_bytes, &ver_v6),
      ("--stark-128-zk", &out_zk1.envelope_bytes, &ver_zk),
    ] {
      // Wrong public statement
      let mut bad_pub = publics.clone();
      bad_pub[0] += Val::ONE;
      assert!(
        ver
          .verify(env_bytes, &bad_pub, &inner_vk_digest, &claim_digest)
          .is_err(),
        "{label}: accepted wrong public statement"
      );

      // Wrong expected inner_vk_digest / claim_digest
      let mut wrong_ivk = inner_vk_digest;
      wrong_ivk[0] ^= 1;
      assert!(
        ver.verify(env_bytes, &publics, &wrong_ivk, &claim_digest).is_err(),
        "{label}: accepted wrong inner VK digest"
      );
      let mut wrong_cd = claim_digest;
      wrong_cd[0] ^= 1;
      assert!(
        ver.verify(env_bytes, &publics, &inner_vk_digest, &wrong_cd).is_err(),
        "{label}: accepted wrong claim digest"
      );

      // Tampered shrinker_vk_digest in envelope
      let mut env = PlonkishEnvelope::from_bytes(env_bytes).unwrap();
      env.header.shrinker_vk_digest[31] ^= 1;
      assert!(
        ver
          .verify(
            &env.to_bytes().unwrap(),
            &publics,
            &inner_vk_digest,
            &claim_digest
          )
          .is_err(),
        "{label}: accepted wrong shrinker VK digest"
      );

      // Bit-flipped proof byte
      let mut env = PlonkishEnvelope::from_bytes(env_bytes).unwrap();
      let mid = env.proof_bytes.len() / 2;
      env.proof_bytes[mid] ^= 0x01;
      assert!(
        ver
          .verify(
            &env.to_bytes().unwrap(),
            &publics,
            &inner_vk_digest,
            &claim_digest
          )
          .is_err(),
        "{label}: accepted corrupted proof byte"
      );

      // Non-zero active bitmap padding bit in compact codec (byte 1 of proof_bytes)
      let mut env = PlonkishEnvelope::from_bytes(env_bytes).unwrap();
      env.proof_bytes[1] |= 0x80;
      assert!(
        ver
          .verify(
            &env.to_bytes().unwrap(),
            &publics,
            &inner_vk_digest,
            &claim_digest
          )
          .is_err(),
        "{label}: accepted noncanonical active bitmap padding"
      );

      // Trailing byte
      let mut trailing = env_bytes.clone();
      trailing.push(0x42);
      assert!(
        ver
          .verify(&trailing, &publics, &inner_vk_digest, &claim_digest)
          .is_err(),
        "{label}: accepted trailing byte"
      );
    }

    // 6. Cross-mode replay attacks (header level AND re-headered raw proof level!)
    assert!(
      ver_zk
        .verify(
          &out_v6.envelope_bytes,
          &publics,
          &inner_vk_digest,
          &claim_digest
        )
        .unwrap_err()
        .contains("cross-mode")
    );
    assert!(
      ver_v6
        .verify(
          &out_zk1.envelope_bytes,
          &publics,
          &inner_vk_digest,
          &claim_digest
        )
        .unwrap_err()
        .contains("cross-mode")
    );
    let raw_v6 =
      PlonkishEnvelope::from_bytes(&out_v6.envelope_bytes).unwrap().proof_bytes;
    let forged_as_zk = PlonkishEnvelope {
      header: PlonkishHeader {
        mode: ShrinkMode::Stark128Zk,
        params,
        compact_encoding: true,
        hops: 1,
        zk_randomizer_width: 4,
        min_log_degree: 8,
        shrinker_vk_digest: *ver_zk.vk_digest(),
        inner_vk_digest,
        claim_digest,
        proof_len: raw_v6.len() as u64,
      },
      proof_bytes: raw_v6,
    }
    .to_bytes()
    .unwrap();
    assert!(
      ver_zk
        .verify(&forged_as_zk, &publics, &inner_vk_digest, &claim_digest)
        .is_err(),
      "v6-zk verifier accepted re-headered raw v6 proof"
    );

    // 7. Unmerged nibble table (16 rows < 256) rejected fail-closed in v6-zk!
    let (c_unmerged, a_unmerged, _) = build_compact_blake3_plonkish_circuit(7);
    let unmerged_opts = PlonkishOptions {
      merge_tables: false,
      merge_blake3_and_tables: false,
      pack_single_circuit: false,
      ..PlonkishOptions::default()
    };
    let err = prove_plonkish_circuit(
      c_unmerged,
      a_unmerged,
      inner_vk_digest,
      claim_digest,
      ShrinkMode::Stark128Zk,
      params,
      unmerged_opts,
      1,
      None,
    )
    .err()
    .expect("v6-zk must reject height-16 nibble table");
    assert!(err.contains("below v6-zk min height"), "{err}");

    // 8. Single-root commitments only: no capped outer
    //    verifier can be derived, and a header declaring a cap is rejected.
    let cap4_params = OuterFriParams { cap_height: 4, ..params };
    let (c_cap4, _, _) = build_compact_blake3_plonkish_circuit(7);
    let err = PlonkishCircuitVerifier::derive(
      c_cap4,
      ShrinkMode::Stark128,
      cap4_params,
      opts,
      1,
    )
    .err()
    .expect("derived a cap_height=4 outer verifier");
    assert!(err.contains("cap_height"), "{err}");
    let mut capped =
      PlonkishEnvelope::from_bytes(&out_v6.envelope_bytes).unwrap();
    capped.header.params = cap4_params;
    let err = ver_v6
      .verify(
        &capped.to_bytes().unwrap(),
        &publics,
        &inner_vk_digest,
        &claim_digest,
      )
      .unwrap_err();
    assert!(err.contains("cap_height"), "{err}");
  }

  fn build_fixed_root_fixture()
  -> (AiurVerifyingKey, FixedRoot, AiurBatchProof, Vec<Val>) {
    use aiur::trace::stark::MEMSEG;
    use multi_stark::batch::BatchMessage;

    // Build a real production-floor Protocol v6 normalized inner BatchProof
    // (lb=4, q=66, qpow=20: 149.03b Johnson, 80.19b UD, 284b conj) matching
    // `FixedRoot`'s segmented ROM policy.
    let cp = CommitmentParameters { log_blowup: 4, cap_height: 0 };
    let fp = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 66,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 20,
    };
    let channel = Val::from_u64(MEMSEG);
    let (system, pk) = System::new(
      GoldilocksBlake3V6Config::new(cp, fp),
      [(2usize, 4usize), (1, 2)].into_iter().map(|(width, height)| {
        CircuitInputs {
          main_width: width + 3,
          preprocessed: Some(RowMajorMatrix::new_col(vec![Val::ZERO; height])),
          lookups: vec![
            Lookup::pull(
              if width == 2 { Expr::main(2) } else { Val::ZERO.into() },
              vec![Expr::main(0), Expr::main(1)],
            ),
            Lookup::push(
              Expr::main(2),
              vec![
                channel.into(),
                Val::from_usize(width).into(),
                Val::ZERO.into(),
              ],
            ),
            Lookup::pull(
              Expr::main(2),
              vec![
                channel.into(),
                Val::from_usize(width).into(),
                Expr::main(3),
              ],
            ),
          ],
          ..Default::default()
        }
      }),
    );
    let inner_vk_bytes = stark_key::to_bytes(&system, cp, fp);
    let inner_vk = AiurVerifyingKey::from_bytes(&inner_vk_bytes).unwrap();
    let fixed = FixedRoot::new(vec![2, 1], vec![(1, 1), (2, 0)], 2).unwrap();

    let expected = vec![Val::from_u32(19), Val::from_u32(39)];
    let messages = [(1u32, 2u32), (2, 4)]
      .into_iter()
      .flat_map(|(width, end)| {
        [
          BatchMessage::pull(vec![channel, Val::from_u32(width), Val::ZERO]),
          BatchMessage::push(vec![
            channel,
            Val::from_u32(width),
            Val::from_u32(end),
          ]),
        ]
      })
      .collect();
    let traces = [(2usize, 4u32, 4usize), (1, 2, 2)]
      .into_iter()
      .map(|(width, end, height)| {
        let row_width = width + 3;
        let mut values = vec![Val::ZERO; row_width * height];
        values[..4].copy_from_slice(&[
          expected[0],
          expected[1],
          Val::ONE,
          Val::from_u32(end),
        ]);
        RowMajorMatrix::new(values, row_width)
      })
      .collect();
    let inner_proof = system.prove_batch(
      &pk,
      vec![ShardInput {
        claims: vec![expected.clone()],
        witness: SystemWitness::from_stage_1(traces, &system),
      }],
      messages,
    );
    inner_vk
      .verify_normalized(std::slice::from_ref(&expected), &inner_proof)
      .unwrap();
    (inner_vk, fixed, inner_proof, expected)
  }

  #[test]
  fn plonkish_fixed_root_roundtrip_and_independent_derivation() {
    #[cfg(feature = "cuda")]
    let _gpu_guard = gpu_test_guard();
    let (inner_vk, fixed, inner_proof, expected) = build_fixed_root_fixture();

    // Production 128-bit floor for both v6 and v6-zk (lb=3 >= 3, 129.13b Johnson,
    // 82.25b CertiFRI UD, 245b conjectured, 8-ary FRI, lfp=8): halves LDE blowup
    // and quotient degree vs lb=4 so the 2^20-row FixedRoot roundtrip stays well
    // within 61.8 GiB CI runners (`COMPACT_400KB_FAST` lb=4 is already covered
    // for both v6 and v6-zk in `plonkish_1circuit_v6_and_v6_zk_roundtrip_...`).
    let outer_params = OuterFriParams {
      log_blowup: 3,
      num_queries: 75,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 20,
      cap_height: 0,
      max_log_arity: 3,
      log_final_poly_len: 8,
    };
    let opts = PlonkishOptions::default();
    let inner_id = fixed.identity(&inner_vk);
    let claim_digest = hash_publics(&expected);

    for mode in [ShrinkMode::Stark128, ShrinkMode::Stark128Zk] {
      // Independent verifier derivation from (inner_vk, FixedRoot) alone!
      let ver = PlonkishCircuitVerifier::derive_fixed_root(
        &inner_vk,
        &fixed,
        mode,
        outer_params,
        opts,
      )
      .unwrap();
      assert_eq!(ver.num_outer_circuits(), 1);
      assert_eq!(ver.hops(), 1);

      let (out, _) = shrink_fixed_root(
        &inner_vk,
        &fixed,
        &inner_proof,
        &expected,
        mode,
        outer_params,
        opts,
        None,
      )
      .unwrap();
      assert_eq!(out.vk_digest, *ver.vk_digest());
      assert_eq!(out.trace_dimensions.len(), 1);
      assert_eq!(out.report.header.mode, mode);
      assert_eq!(out.report.header.hops, 1);
      let rep = ver
        .verify_report(&out.envelope_bytes, &expected, &inner_id, &claim_digest)
        .unwrap();
      assert_eq!(rep.header.mode, mode);
      assert_eq!(rep.header.hops, 1);
      // Tampered hop count (1 -> 2) rejected fail-closed even though 2 <= MAX_PLONKISH_HOPS!
      let mut bad_hops = out.envelope_bytes.clone();
      bad_hops[18] = 2;
      assert!(
        ver.verify(&bad_hops, &expected, &inner_id, &claim_digest).is_err()
      );
      // Wrong public claim rejected fail-closed: against the true digest, and
      // by the proof check when the header is rewritten to the wrong claim's
      // digest (so every digest comparison passes).
      let wrong = [expected[0] + Val::ONE, expected[1]];
      let wrong_digest = hash_publics(&wrong);
      assert!(
        ver
          .verify(&out.envelope_bytes, &wrong, &inner_id, &claim_digest)
          .is_err()
      );
      let mut reheadered =
        PlonkishEnvelope::from_bytes(&out.envelope_bytes).unwrap();
      reheadered.header.claim_digest = wrong_digest;
      let err = ver
        .verify(
          &reheadered.to_bytes().unwrap(),
          &wrong,
          &inner_id,
          &wrong_digest,
        )
        .unwrap_err();
      assert!(err.contains("verification failed"), "{err}");
      eprintln!(
        "[FIXED_ROOT {}] dims={:?} hops={} prove={:.1}ms verify={:.2}ms env={}B ({:.1}KB)",
        mode.cli_flag(),
        out.trace_dimensions,
        rep.header.hops,
        out.prove_ms,
        rep.verify_ms,
        rep.envelope_bytes,
        to_kib(rep.envelope_bytes),
      );
    }
  }

  #[test]
  fn plonkish_multihop_planner_and_comp_cap_slack() {
    let (inner_vk, fixed, _inner_proof, _expected) = build_fixed_root_fixture();

    // 1. Default max_trace_height (2^24): small FixedRoot plans 1 direct Final hop.
    let c1 = fixed.circuit(&inner_vk, VerifierLimits::default()).unwrap();
    let plan1 = plan_hop_lowering(
      c1,
      PlonkishOptions::default(),
      ShrinkMode::Stark128,
      OuterFriParams::COMPACT_400KB_BALANCED,
      1,
    )
    .unwrap();
    match plan1 {
      HopLowering::Final { definitions, merged, .. } => {
        assert_eq!(definitions.len(), 1);
        assert!(merged.as_ref().is_some_and(MergedLayout::is_merged));
      },
      HopLowering::Intermediate { .. } => {
        panic!("expected 1-hop Final plan on small FixedRoot at 2^24");
      },
    }

    // 2. Tighter max_trace_height below B3_All active height: planner automatically
    //    selects an in-circuit verifiable Intermediate hop (cap=0, mla=1, lfp=0)
    //    instead of silently falling back to unmerged circuits that fail lfp=8.
    let c2 = fixed.circuit(&inner_vk, VerifierLimits::default()).unwrap();
    let est = c2.multi_stark_layout_with_max_height(1 << 24).unwrap();
    let b3_lb = b3_lower_bound(&est).expect("compact BLAKE3 custom traces");
    let tight_max = 1usize << (b3_lb.saturating_sub(1).ilog2());
    assert!(tight_max < b3_lb);
    let tight_opts = PlonkishOptions {
      max_trace_height: tight_max,
      ..PlonkishOptions::default()
    };
    let plan2 = plan_hop_lowering(
      c2,
      tight_opts,
      ShrinkMode::Stark128Zk,
      OuterFriParams::COMPACT_400KB_BALANCED,
      1,
    )
    .unwrap();
    match plan2 {
      HopLowering::Intermediate { hop_params, .. } => {
        assert_eq!(hop_params.cap_height, 0);
        assert_eq!(hop_params.max_log_arity, 1);
        assert_eq!(hop_params.log_final_poly_len, 0);
        hop_params.check().unwrap();
      },
      HopLowering::Final { .. } => {
        panic!(
          "expected Intermediate hop when max_trace_height ({tight_max}) < b3_lower_bound ({b3_lb})"
        );
      },
    }

    // 3. Verify intermediate hop parameter selection by height threshold.
    assert_eq!(
      intermediate_hop_params_for_height(1 << 25),
      OuterFriParams::HOP_INTERMEDIATE_FAST
    );
    assert_eq!(
      intermediate_hop_params_for_height(1 << 24),
      OuterFriParams::HOP_INTERMEDIATE_COMPACT
    );

    // 4. Verify b3_lower_bound & 3x comp-cap heuristic on real Hop-1c dimensions:
    //    custom_traces[0..6] = [2^21, 2^21, 2^21, 2^21, 2^18, 2^20], used_rows = 17,392,784.
    let hop1c_est = multi_stark::plonkish::MultiStarkLayout {
      used_rows: 17_392_784,
      main_height: 17_825_792,
      main_heights: vec![1 << 24, 1 << 20],
      main_width: 3,
      preprocessed_width: 17,
      table_heights: vec![16, 256, 16],
      custom_traces: vec![
        (1 << 21, 32, 14),
        (1 << 21, 40, 14),
        (1 << 21, 32, 14),
        (1 << 21, 40, 14),
        (1 << 18, 12, 8),
        (1 << 20, 4, 18),
        (65536, 1, 3),
        (512, 1, 4),
        (256, 1, 1),
      ],
      advice_cells: 0,
      preprocessed_cells: 0,
      trace_field_bytes: 0,
    };
    let h0 = hop1c_est.custom_traces[0].0;
    let b3_est = (h0 * 4).next_power_of_two().min(1 << 24);
    assert_eq!(b3_est, 1 << 23);
    assert!(hop1c_est.used_rows > b3_est * 2, "old 2x cap missed by 3.6%");
    assert!(hop1c_est.used_rows <= b3_est * 3, "new 3x cap fits 2^23 cleanly");
    assert!(b3_lower_bound(&hop1c_est).unwrap() <= (1 << 23));
  }

  #[cfg(feature = "cuda")]
  #[test]
  fn cuda_plonkish_compact_400kb_balanced_and_fixed_root_gpu_prove_cpu_verify()
  {
    let _gpu_guard = gpu_test_guard();
    const MAX_COMPACT_BYTES: usize = 425 * 1024;
    let params = OuterFriParams::COMPACT_400KB_BALANCED;
    let opts = PlonkishOptions::default();
    assert!(params.is_cuda_compatible());

    // 1. 1-circuit merged BLAKE3 Plonkish circuit -> COMPACT_400KB_BALANCED on
    //    GPU (`device = Some(0)`) for both --stark-128 (v6) and --stark-128-zk
    //    (v6-zk), independently verified on CPU.
    let inner_vk_digest = [0xCC; 32];
    let (_, _, publics) = build_compact_blake3_plonkish_circuit(11);
    let claim_digest = hash_publics(&publics);

    for mode in [ShrinkMode::Stark128, ShrinkMode::Stark128Zk] {
      let (circuit_der, _, _) = build_compact_blake3_plonkish_circuit(11);
      let ver =
        PlonkishCircuitVerifier::derive(circuit_der, mode, params, opts, 1)
          .unwrap();
      assert_eq!(ver.num_outer_circuits(), 1);

      let (circuit, assignment, _) = build_compact_blake3_plonkish_circuit(11);
      let (out, _) = prove_plonkish_circuit(
        circuit,
        assignment,
        inner_vk_digest,
        claim_digest,
        mode,
        params,
        opts,
        1,
        Some(0),
      )
      .unwrap();
      assert_eq!(out.trace_dimensions.len(), 1);
      assert_eq!(out.vk_digest, *ver.vk_digest());
      assert!(
        out.envelope_bytes.len() <= MAX_COMPACT_BYTES,
        "CUDA COMPACT_400KB_BALANCED {} envelope {} B ({:.1} KiB) exceeded 425 KiB cap",
        mode.cli_flag(),
        out.envelope_bytes.len(),
        to_kib(out.envelope_bytes.len()),
      );
      let rep = ver
        .verify_report(
          &out.envelope_bytes,
          &publics,
          &inner_vk_digest,
          &claim_digest,
        )
        .unwrap();
      assert_eq!(rep.header.mode, mode);
      assert_eq!(rep.header.params, params);
      eprintln!(
        "[CUDA COMPACT_400KB_BALANCED {}] dims={:?} gpu_prove={:.1}ms cpu_verify={:.2}ms env={}B ({:.1} KiB) | {}",
        mode.cli_flag(),
        out.trace_dimensions,
        out.prove_ms,
        rep.verify_ms,
        rep.envelope_bytes,
        to_kib(rep.envelope_bytes),
        out.breakdown.summary_line(),
      );
    }

    // 2. FixedRoot end-to-end on GPU (device=Some(0)) for both v6 and v6-zk,
    //    independently verified on CPU via `derive_fixed_root`.
    let (inner_vk, fixed, inner_proof, expected) = build_fixed_root_fixture();
    let inner_id = fixed.identity(&inner_vk);
    let fixed_claim_digest = hash_publics(&expected);
    let mut envelopes = Vec::with_capacity(2);

    for mode in [ShrinkMode::Stark128, ShrinkMode::Stark128Zk] {
      let ver = PlonkishCircuitVerifier::derive_fixed_root(
        &inner_vk, &fixed, mode, params, opts,
      )
      .unwrap();
      assert_eq!(ver.num_outer_circuits(), 1);

      let (out, _) = shrink_fixed_root_1hop(
        &inner_vk,
        &fixed,
        &inner_proof,
        &expected,
        mode,
        params,
        opts,
        Some(0),
      )
      .unwrap();
      assert_eq!(out.trace_dimensions.len(), 1);
      assert_eq!(out.vk_digest, *ver.vk_digest());
      assert!(
        out.envelope_bytes.len() <= MAX_COMPACT_BYTES,
        "CUDA FixedRoot {} envelope {} B ({:.1} KiB) exceeded 425 KiB cap",
        mode.cli_flag(),
        out.envelope_bytes.len(),
        to_kib(out.envelope_bytes.len()),
      );
      let rep = ver
        .verify_report(
          &out.envelope_bytes,
          &expected,
          &inner_id,
          &fixed_claim_digest,
        )
        .unwrap();
      assert_eq!(rep.header.mode, mode);
      assert_eq!(rep.header.params, params);
      assert!(
        ver
          .verify(
            &out.envelope_bytes,
            &[expected[0] + Val::ONE, expected[1]],
            &inner_id,
            &hash_publics(&[expected[0] + Val::ONE, expected[1]]),
          )
          .is_err(),
        "CUDA FixedRoot {} accepted wrong public statement",
        mode.cli_flag()
      );
      eprintln!(
        "[CUDA FIXED_ROOT COMPACT_400KB_BALANCED {}] dims={:?} gpu_prove={:.1}ms cpu_verify={:.2}ms env={}B ({:.1} KiB) | {}",
        mode.cli_flag(),
        out.trace_dimensions,
        out.prove_ms,
        rep.verify_ms,
        rep.envelope_bytes,
        to_kib(rep.envelope_bytes),
        out.breakdown.summary_line(),
      );
      envelopes.push((ver, out.envelope_bytes));
    }

    // Cross-mode replay on GPU-proved FixedRoot envelopes rejected fail-closed!
    assert!(
      envelopes[0]
        .0
        .verify(&envelopes[1].1, &expected, &inner_id, &fixed_claim_digest)
        .unwrap_err()
        .contains("cross-mode")
    );
    assert!(
      envelopes[1]
        .0
        .verify(&envelopes[0].1, &expected, &inner_id, &fixed_claim_digest)
        .unwrap_err()
        .contains("cross-mode")
    );
  }

  #[cfg(feature = "cuda")]
  #[test]
  #[ignore = "requires exclusive access to a CUDA device: sets MULTI_STARK_SPILL_DIR and reserves VRAM"]
  fn cuda_plonkish_spilled_v6_and_v6zk_gpu_prove_cpu_verify() {
    let _gpu_guard = gpu_test_guard();
    let spill_dir = std::env::temp_dir()
      .join(format!("stark-shrinker-cuda-spill-{}", std::process::id()));
    let _ = std::fs::remove_dir_all(&spill_dir);
    std::fs::create_dir_all(&spill_dir).unwrap();

    struct EnvGuard {
      prev: Option<std::ffi::OsString>,
      dir: std::path::PathBuf,
    }
    impl Drop for EnvGuard {
      fn drop(&mut self) {
        // SAFETY: ignored exclusive GPU test runs with `--test-threads=1`.
        unsafe {
          match &self.prev {
            Some(v) => std::env::set_var("MULTI_STARK_SPILL_DIR", v),
            None => std::env::remove_var("MULTI_STARK_SPILL_DIR"),
          }
        }
        let _ = std::fs::remove_dir_all(&self.dir);
      }
    }
    let prev = std::env::var_os("MULTI_STARK_SPILL_DIR");
    // SAFETY: ignored exclusive GPU test runs with `--test-threads=1`.
    unsafe {
      std::env::set_var("MULTI_STARK_SPILL_DIR", &spill_dir);
    }
    let _env_guard = EnvGuard { prev, dir: spill_dir.clone() };

    let params = OuterFriParams::COMPACT_400KB_FAST;
    let opts = PlonkishOptions::default();
    let inner_vk_digest = [0xDD; 32];
    let (_, _, publics) = build_compact_blake3_plonkish_circuit(11);
    let claim_digest = hash_publics(&publics);

    // 1. Reference resident v6 envelope on GPU.
    let (circuit_ref, assignment_ref, _) =
      build_compact_blake3_plonkish_circuit(11);
    let (out_v6_res, _) = prove_plonkish_circuit(
      circuit_ref,
      assignment_ref,
      inner_vk_digest,
      claim_digest,
      ShrinkMode::Stark128,
      params,
      opts,
      1,
      Some(0),
    )
    .unwrap();

    // 2. Force disk spilling under a VRAM reservation and prove both v6 and
    //    v6-zk via `prove_plonkish_circuit(..., Some(0))`.
    {
      let _reservation =
        multi_stark::cuda::DeviceMemoryReservation::new(0, 1usize << 40);
      for mode in [ShrinkMode::Stark128, ShrinkMode::Stark128Zk] {
        let (circuit_der, _, _) = build_compact_blake3_plonkish_circuit(11);
        let ver =
          PlonkishCircuitVerifier::derive(circuit_der, mode, params, opts, 1)
            .unwrap();
        let (circuit, assignment, _) =
          build_compact_blake3_plonkish_circuit(11);
        let (out, _) = prove_plonkish_circuit(
          circuit,
          assignment,
          inner_vk_digest,
          claim_digest,
          mode,
          params,
          opts,
          1,
          Some(0),
        )
        .unwrap();
        assert_eq!(out.trace_dimensions.len(), 1);
        assert_eq!(out.vk_digest, *ver.vk_digest());
        if mode == ShrinkMode::Stark128 {
          assert_eq!(
            out.envelope_bytes, out_v6_res.envelope_bytes,
            "v6 spilled CUDA shrinker envelope must match resident CUDA envelope byte-for-byte"
          );
        }
        let rep = ver
          .verify_report(
            &out.envelope_bytes,
            &publics,
            &inner_vk_digest,
            &claim_digest,
          )
          .unwrap();
        assert_eq!(rep.header.mode, mode);
        assert_eq!(rep.header.params, params);
      }
    }

    assert_eq!(
      multi_stark::p3_adapter::spill::active_spill_files(),
      0,
      "all CUDA shrinker spill files must be cleaned up"
    );
  }

  #[test]
  #[ignore = "heavy multi-config 1-circuit cloud benchmark; run explicitly on cloud box"]
  fn plonkish_3circuit_merged_benchmark() {
    let (vk_sm, prof_sm, schema_sm, stmt_sm, proof_sm) =
      build_inner_v6_batch(2, 8);
    let inner_sm_bytes = proof_sm.to_bytes().unwrap().len();
    eprintln!(
      "\n================ 1-CIRCUIT UNIFIED PLONKISH SHRINKER BENCHMARK (4 circuits, inner={} B) ================",
      inner_sm_bytes
    );

    let opts = PlonkishOptions::default(); // pack_single_circuit=true -> num_circuits == 1!

    let configs: Vec<(&str, OuterFriParams)> = vec![
      (
        "1circ_lb4_q66_qpow20_mla1_lfp8_CUDA",
        OuterFriParams {
          log_blowup: 4,
          num_queries: 66,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 20,
          cap_height: 0,
          max_log_arity: 1,
          log_final_poly_len: 8,
        },
      ),
      (
        "1circ_lb4_q66_qpow20_mla3_lfp8",
        OuterFriParams {
          log_blowup: 4,
          num_queries: 66,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 20,
          cap_height: 0,
          max_log_arity: 3,
          log_final_poly_len: 8,
        },
      ),
      (
        "1circ_lb4_q62_qpow24_mla3_lfp8",
        OuterFriParams {
          log_blowup: 4,
          num_queries: 62,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 24,
          cap_height: 0,
          max_log_arity: 3,
          log_final_poly_len: 8,
        },
      ),
      (
        "1circ_lb4_q60_qpow26_mla3_lfp8",
        OuterFriParams {
          log_blowup: 4,
          num_queries: 60,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 26,
          cap_height: 0,
          max_log_arity: 3,
          log_final_poly_len: 8,
        },
      ),
      (
        "1circ_lb4_q58_qpow28_mla3_lfp8",
        OuterFriParams {
          log_blowup: 4,
          num_queries: 58,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 28,
          cap_height: 0,
          max_log_arity: 3,
          log_final_poly_len: 8,
        },
      ),
      (
        "1circ_lb4_q55_qpow30_mla3_lfp8",
        OuterFriParams {
          log_blowup: 4,
          num_queries: 55,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 30,
          cap_height: 0,
          max_log_arity: 3,
          log_final_poly_len: 8,
        },
      ),
    ];

    for (label, params) in configs {
      for mode in [ShrinkMode::Stark128, ShrinkMode::Stark128Zk] {
        let (out, _ver) = shrink_single_batch_1hop(
          &vk_sm,
          prof_sm.clone(),
          schema_sm.clone(),
          &proof_sm,
          &stmt_sm,
          mode,
          params,
          opts,
          None,
        )
        .unwrap_or_else(|e| panic!("{label} {} failed: {e}", mode.cli_flag()));
        assert_eq!(out.trace_dimensions.len(), 1, "expected 1 packed circuit");
        eprintln!(
          "[{label} {}] dims={:?} prove={:.1}ms verify={:.2}ms rss={:.0}MiB env={}B ({:.1}KB) | {}",
          mode.cli_flag(),
          out.trace_dimensions,
          out.prove_ms,
          out.verify_ms,
          peak_rss_mib(),
          out.envelope_bytes.len(),
          to_kib(out.envelope_bytes.len()),
          out.breakdown.summary_line(),
        );
      }
    }
  }

  #[test]
  #[ignore = "heavy 45-circuit ix_aggr-scale cloud benchmark; run explicitly on cloud box"]
  fn plonkish_45circuit_aggr_benchmark() {
    let (vk_big, prof_big, schema_big, stmt_big, proof_big) =
      build_inner_v6_batch(43, 12); // 45 circuits total!
    let inner_bytes = proof_big.to_bytes().unwrap().len();
    eprintln!(
      "\n================ 45-CIRCUIT ix_aggr-SCALE BENCHMARK (45 circuits, inner={} B / {:.1} KB) ================",
      inner_bytes,
      to_kib(inner_bytes)
    );

    let opts = PlonkishOptions::default(); // 1-circuit unified packer!
    // Measure lb=4 (v6) and lb=3 (both v6 & v6-zk) in RAM on 45-circuit ix_aggr scale!
    let runs: Vec<(&str, ShrinkMode, OuterFriParams)> = vec![
      (
        "aggr45_1circ_lb4_q62_qpow24_mla3_lfp8",
        ShrinkMode::Stark128,
        OuterFriParams::COMPACT_400KB_FAST,
      ),
      (
        "aggr45_1circ_lb4_q58_qpow28_mla3_lfp8",
        ShrinkMode::Stark128,
        OuterFriParams::COMPACT_400KB_BALANCED,
      ),
      (
        "aggr45_1circ_lb3_q69_qpow28_mla3_lfp8",
        ShrinkMode::Stark128,
        OuterFriParams {
          log_blowup: 3,
          num_queries: 69,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 28,
          cap_height: 0,
          max_log_arity: 3,
          log_final_poly_len: 8,
        },
      ),
      (
        "aggr45_1circ_lb3_q69_qpow28_mla3_lfp8",
        ShrinkMode::Stark128Zk,
        OuterFriParams {
          log_blowup: 3,
          num_queries: 69,
          commit_proof_of_work_bits: 0,
          query_proof_of_work_bits: 28,
          cap_height: 0,
          max_log_arity: 3,
          log_final_poly_len: 8,
        },
      ),
    ];

    for (label, mode, params) in runs {
      let (out, _ver) = shrink_single_batch_1hop(
        &vk_big,
        prof_big.clone(),
        schema_big.clone(),
        &proof_big,
        &stmt_big,
        mode,
        params,
        opts,
        None,
      )
      .unwrap_or_else(|e| panic!("{label} {} failed: {e}", mode.cli_flag()));
      eprintln!(
        "[{label} {}] dims={:?} prove={:.1}ms verify={:.2}ms rss={:.0}MiB env={}B ({:.1}KB) | {}",
        mode.cli_flag(),
        out.trace_dimensions,
        out.prove_ms,
        out.verify_ms,
        peak_rss_mib(),
        out.envelope_bytes.len(),
        to_kib(out.envelope_bytes.len()),
        out.breakdown.summary_line(),
      );
    }
  }
}
