//! Protocol `v6-zk` zero-knowledge standalone STARK backend for Aiur programs.
//!
//! Shares circuit lowering, vectorized ROM (`C6`), fixed-table setup, and
//! Rayon-parallel witness generation with [`super::Backend`], while targeting
//! [`GoldilocksBlake3V6ZkConfig`] (`Fp^3 = Fp[X]/(X^3 - X - 1)`,
//! `FriBatching::Tensor`, 2x odd-coset hiding PCS, `W_R = 4` randomizer
//! polynomial, 128-bit BLAKE3-CTR leaf salts, telescoping half-stride quotient
//! blinding, and blinded cross-circuit accumulators).
use super::*;
use multi_stark::{
  config::ProofConfig,
  p3_adapter::{
    domain_blake3::Blake3Domain,
    zk::{ZK_RANDOMIZER_WIDTH, min_zk_log_degree},
  },
  system::compute_vk_digest_with_domain,
  types::GoldilocksBlake3V6ZkConfig,
};

pub type ZkProof = multi_stark::prover::Proof<GoldilocksBlake3V6ZkConfig>;

/// Standalone Protocol `v6-zk` zero-knowledge backend for an Aiur [`TracePlan`].
pub struct ZkBackend<'p, 'a, B: WitnessField = PrimeField> {
  plan: Shared<'p, TracePlan<'a, B>>,
  system: System<GoldilocksBlake3V6ZkConfig>,
  key: ProverKey<GoldilocksBlake3V6ZkConfig>,
  tables: Vec<tables::FixedTable>,
  rom: rom::Rom,
  lookup_plans: Vec<witness::LookupPlan>,
  member_lookup_plans: Vec<witness::MemberLookupPlan>,
  circuit_chips: Vec<Vec<usize>>,
  members: Vec<Vec<usize>>,
  placements: Vec<grouping::Placement>,
  parameters: Parameters,
}

impl<'p, 'a, B: WitnessField> ZkBackend<'p, 'a, B> {
  /// Build a `v6-zk` backend on CPU, enforcing the 128-bit security floor.
  pub fn new(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
  ) -> Result<Self, String> {
    Self::build(plan, parameters, None, true)
  }

  /// Build a `v6-zk` backend targeting an optional CUDA device (rejects a
  /// requested GPU device in CPU-only builds).
  pub fn new_on_device(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    device: Option<i32>,
  ) -> Result<Self, String> {
    Self::build(plan, parameters, device, true)
  }

  /// Build a CPU `v6-zk` backend for verification (ignores GPU placement).
  pub fn for_verification(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
  ) -> Result<Self, String> {
    Self::build(plan, parameters, None, true)
  }

  /// Build a `v6-zk` backend without enforcing the 128-bit security floor
  /// (for unit tests exercising toy parameters). Never trust proofs verified
  /// under this constructor in production.
  #[doc(hidden)]
  pub fn new_below_floor(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
  ) -> Result<Self, String> {
    Self::build(plan, parameters, None, false)
  }

  fn build(
    plan: impl Into<Shared<'p, TracePlan<'a, B>>>,
    parameters: Parameters,
    device: Option<i32>,
    floor: bool,
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
      return Err(
        "multi-stark v6-zk adapter requires the Goldilocks field".into(),
      );
    }
    let ext_degree =
      multi_stark::system::extension_params::<GoldilocksBlake3V6ZkConfig>()
        .degree;
    let min_log_deg = min_zk_log_degree(parameters.num_queries, ext_degree);
    let max_log_deg = 32usize
      .checked_sub(1 + parameters.log_blowup)
      .ok_or("log_blowup exceeds Goldilocks two-adicity")?;
    if min_log_deg > max_log_deg {
      return Err(format!(
        "v6-zk min_log_degree ({min_log_deg}) exceeds max_log_degree ({max_log_deg})"
      ));
    }
    let min_height = 1usize << min_log_deg;

    let rom = rom::Rom::new(&plan, RomLayout::Vectorized);
    let mut inputs = vec![];
    let mut names = vec![];
    let placements = grouping::build(&plan, &rom, &mut inputs, &mut names)?;
    let function_circuits = inputs.len();
    let tables = tables::fixed_tables(
      &plan,
      &mut inputs,
      &mut names,
      parameters.log_blowup,
      true,
      min_height,
      true,
    )?;
    // Standalone (non-segmented) ROM avoids cleartext MEMSEG count leakage in
    // zero-knowledge proofs while preserving full address uniqueness.
    rom.append_circuits(&mut inputs, &mut names, false)?;

    // In v6-zk, `quotient_degree_for(true) = max(d, 1).next_power_of_two() <= blowup`,
    // which holds iff `d <= 2^log_blowup`.
    let blowup = 1usize << parameters.log_blowup;
    for (input, name) in inputs.iter().zip(&names) {
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
      if user_degree.max(lookup_degree) > blowup {
        return Err(format!(
          "{name}: increase log_blowup for v6-zk constraint degree {} (blowup {blowup})",
          user_degree.max(lookup_degree)
        ));
      }
    }

    let config = GoldilocksBlake3V6ZkConfig::with_options(
      parameters.commitment(),
      parameters.fri(),
      FriBatching::Tensor,
      ZK_RANDOMIZER_WIDTH,
      device,
    );
    let (mut system, key) = System::new(config, inputs);
    for circuit in &mut system.circuits {
      lookup_groups::retune_with_zk(circuit, blowup, ext_degree, true);
    }
    system.vk_digest = compute_vk_digest_with_domain::<Val, ExtVal3>(
      &system.circuits,
      Blake3Domain::ZkVerifyingKey,
    );

    let lookup_plans = system
      .circuits
      .iter()
      .map(|circuit| witness::LookupPlan::compile(&circuit.graph))
      .collect::<Result<_, _>>()?;
    let member_lookup_plans =
      witness::compile_member_lookup_plans(&placements, &system.circuits)?;
    let mut circuit_chips = vec![vec![]; function_circuits];
    for (chip, placement) in placements.iter().enumerate() {
      circuit_chips[placement.circuit].push(chip);
    }
    let mut members = vec![vec![]; function_circuits];
    for (function, &chip) in plan.members.iter().enumerate() {
      members[placements[chip].circuit].push(function);
    }

    Ok(Self {
      plan,
      system,
      key,
      tables,
      rom,
      lookup_plans,
      member_lookup_plans,
      circuit_chips,
      members,
      placements,
      parameters,
    })
  }

  fn witness_view(&self) -> witness::WitnessView<'_, '_, B> {
    witness::WitnessView {
      plan: &self.plan,
      circuits: &self.system.circuits,
      tables: &self.tables,
      rom: &self.rom,
      lookup_plans: &self.lookup_plans,
      member_lookup_plans: &self.member_lookup_plans,
      circuit_chips: &self.circuit_chips,
      members: &self.members,
      placements: &self.placements,
    }
  }

  pub const fn parameters(&self) -> Parameters {
    self.parameters
  }

  pub const fn system(&self) -> &System<GoldilocksBlake3V6ZkConfig> {
    &self.system
  }

  pub fn min_log_degree(&self) -> usize {
    self.system.config.min_log_degree()
  }

  pub fn zk_randomizer_width(&self) -> usize {
    self.system.config.zk_randomizer_width()
  }

  pub fn claim(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
  ) -> Result<Vec<Val>, String> {
    build_claim(&self.plan, entry, args, output)
  }

  fn check_shape(&self, active: &[bool], degrees: &[u8]) -> Result<(), String> {
    check_shape_for(
      &self.system.circuits,
      self.members.len(),
      self.tables.len(),
      &self.rom,
      self.parameters.log_blowup,
      1,
      self.system.config.min_log_degree(),
      active,
      degrees,
    )
  }

  /// Populate all stage-one traces and lookup buffers from `record`, padding
  /// every active dynamic circuit to at least `2^min_log_degree`.
  pub fn generate(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
  ) -> Result<SystemWitness<Val>, String> {
    let min_height = 1usize << self.system.config.min_log_degree();
    let witness = self.witness_view().generate_with_min_active_height::<true>(
      record,
      Some((entry, args)),
      min_height,
    )?;
    let (active, degrees) =
      trace_shape_for(&self.system.circuits, &witness.traces, &[])?;
    self.check_shape(&active, &degrees)?;
    Ok(witness)
  }

  /// Populate only stage-one main traces from `record` (skipping upfront host
  /// lookup buffer materialization), padding every active dynamic circuit to at
  /// least `2^min_log_degree`. Pair with [`Self::prove_streaming`].
  pub fn generate_stage_1(
    &self,
    record: &Execution<B>,
    entry: &str,
    args: &[B::Element],
  ) -> Result<Vec<RowMajorMatrix<Val>>, String> {
    let min_height = 1usize << self.system.config.min_log_degree();
    let witness =
      self.witness_view().generate_with_min_active_height::<false>(
        record,
        Some((entry, args)),
        min_height,
      )?;
    let (active, degrees) =
      trace_shape_for(&self.system.circuits, &witness.traces, &[])?;
    self.check_shape(&active, &degrees)?;
    Ok(witness.traces)
  }

  /// Prove a prepared `v6-zk` witness for `entry(args) = output`.
  pub fn prove(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    witness: SystemWitness<Val>,
  ) -> Result<ZkProof, String> {
    let claim = self.claim(entry, args, output)?;
    let (active, degrees) =
      trace_shape_for(&self.system.circuits, &witness.traces, &[])?;
    self.check_shape(&active, &degrees)?;
    if witness.lookups.len() != self.system.circuits.len() {
      return Err("wrong lookup witness count".into());
    }
    Ok(self.system.prove(&self.key, &claim, witness))
  }

  /// Prove a `v6-zk` proof directly from stage-one main traces, evaluating
  /// lookup messages lazily per circuit instead of holding all host lookup
  /// buffers in memory simultaneously.
  pub fn prove_streaming(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    traces: Vec<RowMajorMatrix<Val>>,
  ) -> Result<ZkProof, String> {
    let claim = self.claim(entry, args, output)?;
    let (active, degrees) =
      trace_shape_for(&self.system.circuits, &traces, &[])?;
    self.check_shape(&active, &degrees)?;
    Ok(self.system.prove_streaming(&self.key, &claim, traces))
  }

  /// Verify a `v6-zk` proof using the trusted compiled system and public claim.
  pub fn verify(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    proof: &ZkProof,
  ) -> Result<(), String> {
    let claim = self.claim(entry, args, output)?;
    self.check_shape(&proof.active, &proof.log_degrees)?;
    self
      .system
      .verify(&claim, proof)
      .map_err(|e| format!("v6-zk STARK verification failed: {e:?}"))
  }
}
