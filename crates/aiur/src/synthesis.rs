use multi_stark::{
  batch::{BatchProof, Retention},
  expr::Expr,
  lookup::Lookup,
  p3_field::PrimeCharacteristicRing,
  p3_matrix::dense::RowMajorMatrix,
  system::{CircuitInputs, ProverKey, System},
  types::{
    CommitmentParameters, FriParameters, GoldilocksBlake3Config, PcsError,
  },
  verifier::VerificationError,
};

use crate::{
  G,
  bytecode::{FunIdx, Toplevel},
  execute::{ExecError, IOBuffer, QueryRecord},
  function_channel,
  gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2},
  memory::Memory,
  shard::{RowIndex, ShardPlan},
};

/// The concrete STARK configuration Aiur instantiates multi-stark with.
pub type AiurConfig = GoldilocksBlake3Config;
/// A proof under [`AiurConfig`]: a batch of one or more trace shards proven
/// under shared lookup challenges (see [`crate::shard`]). A proof of an
/// unsharded execution is the one-shard batch.
pub type AiurProof = BatchProof<AiurConfig>;
/// What a batch prover keeps of each shard across its barrier.
pub use multi_stark::batch::Retention as ShardRetention;

/// Why an [`AiurProof`] was rejected.
#[derive(Debug)]
pub enum AiurVerificationError {
  /// The batch violates Aiur's policy over multi-stark's batch protocol:
  /// the claim, or the `memseg` closure messages, are not what one
  /// execution's proof carries (see `AiurSystem::check_batch_policy`).
  Policy(String),
  /// The multi-stark batch itself failed to verify.
  Stark(VerificationError<PcsError>),
}

impl From<VerificationError<PcsError>> for AiurVerificationError {
  fn from(error: VerificationError<PcsError>) -> Self {
    Self::Stark(error)
  }
}

/// The prover RAM model's phase breakdown; `peak` is the number the
/// budget gate compares (see [`AiurSystem::peak_prove_bytes`]).
pub struct PeakProveBytes {
  pub phase_witness: usize,
  pub phase_stage2: usize,
  pub phase_open: usize,
  pub preprocessed: usize,
  /// What a proof holds of its stage 1 once committed: the stage-1 LDEs,
  /// their Merkle tree and the lookup witness — the state a batch prover
  /// retains per shard across its barrier under `Retention::Retain`.
  pub retained_stage_1: usize,
  pub peak: usize,
}

// The allocation-schedule model below is deliberately structural, but the
// process RSS also contains allocator/runtime residency that it does not name.
// Across the 168 completed Mathlib shard proofs at multi-stark 2892243e,
// measured RSS / analytic peak had median 1.0678 and maximum under-prediction
// 1.0714. A 7.5% envelope covers the full sample with a small margin. The
// workspace now pins a8aab731; retain this historical guard, but re-calibrate
// before treating it as a full-scale safety bound for the new prover.
const PROVER_RSS_CALIBRATION_NUMERATOR: usize = 43;
const PROVER_RSS_CALIBRATION_DENOMINATOR: usize = 40;

/// Extension degree of the lookup argument's challenge field: the number of
/// base-field columns behind every stage-2 accumulator and quotient column.
pub(crate) const EXTENSION_DEGREE: usize =
  <multi_stark::types::ExtVal as multi_stark::p3_field::BasedVectorSpace<G>>::DIMENSION;

pub(crate) fn calibrate_prover_rss(analytic_peak: usize) -> usize {
  analytic_peak
    .checked_mul(PROVER_RSS_CALIBRATION_NUMERATOR)
    .map_or(usize::MAX, |scaled| {
      scaled.div_ceil(PROVER_RSS_CALIBRATION_DENOMINATOR)
    })
}

/// Outcome of a budget-gated prove
/// ([`AiurSystem::prove_ixvm_within_budget`]). Only the case that ran a
/// STARK carries a proof; the other two report the measured peak the
/// caller decides with.
// One short-lived value per prove; the variant size gap is irrelevant.
#[allow(clippy::large_enum_variant)]
pub enum GatedProve {
  /// Fit the budget; proven from the gating record.
  Proved { claim: Vec<G>, proof: AiurProof, peak: usize },
  /// Over budget: the record was dropped, and `parts` is the count
  /// [`AiurSystem::suggested_split_parts`] projects will fit.
  Split { peak: usize, parts: usize },
  /// `exec_only` with a fitting peak: measured, nothing left to do.
  Measured { peak: usize },
}

pub struct AiurSystem {
  toplevel: Toplevel,
  // perhaps remove the key from the system in verifier only mode?
  key: ProverKey<AiurConfig>,
  /// The parameters the system's config was built from, kept for the
  /// verifying-key codec (the config itself doesn't expose them back).
  pub(crate) commitment_parameters: CommitmentParameters,
  pub(crate) fri_parameters: FriParameters,
  pub(crate) system: System<AiurConfig>,
  /// Per-circuit lookup-slot argument widths (in system order), retained so
  /// the witness builder can size its `LookupValues` without reading them
  /// back off the (now AIR-free) compiled circuits.
  slot_widths: Vec<Vec<usize>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CircuitType {
  Function { idx: usize },
  Memory { width: usize },
  Bytes1,
  Bytes2,
}

/// Shape of one compiled circuit, as needed by the Lean-side FFT cost model
/// (`Ix/Aiur/Statistics.lean`). Heights of function and memory circuits are
/// execution-dependent and are NOT part of the shape; `preprocessed_height`
/// doubles as the fixed trace height of the byte-gadget circuits (256 and
/// 65536), whose witness builders always emit the full table.
pub struct CircuitShape {
  pub main_width: usize,
  pub stage2_width: usize,
  pub quotient_degree: usize,
  pub preprocessed_width: usize,
  pub preprocessed_height: usize,
}

/// Raw row count of a circuit under `record`, ceil-divided into `parts`
/// even shares — `parts = 1` is the record's exact heights. A function
/// circuit's rows are the sum over its member functions (one, unless the
/// toplevel groups functions), every query entry included: a
/// zero-multiplicity hint entry commits no row, so this bounds the trace
/// from above. The byte gadgets keep their fixed heights: they are the same
/// size in every shard and are most of the peak model's floor, which
/// dividing cannot shrink.
fn raw_of<'a>(
  toplevel: &'a Toplevel,
  record: &'a QueryRecord,
  parts: usize,
) -> impl Fn(usize, &CircuitType) -> usize + 'a {
  move |_, ct| match ct {
    CircuitType::Function { idx } => toplevel.circuits[*idx]
      .members
      .iter()
      .map(|&member| record.function_queries[member].len())
      .sum::<usize>()
      .div_ceil(parts),
    CircuitType::Memory { width } => {
      record.memory_queries.get(width).map_or(0, |m| m.len().div_ceil(parts))
    },
    CircuitType::Bytes1 => 256,
    CircuitType::Bytes2 => 65536,
  }
}

/// A record and its IO buffer as a supplier hands them to the batch prover
/// ([`AiurSystem::prove_record_supplier`]): borrowed from the caller, or
/// owned by the prover until it moves on to the next record.
pub enum Supplied<'a> {
  Borrowed(&'a QueryRecord, &'a IOBuffer),
  Owned(Box<QueryRecord>, Box<IOBuffer>),
  /// A record the supplier keeps a reference to as well, e.g. one it
  /// retains for the second round.
  Shared(std::sync::Arc<(Box<QueryRecord>, Box<IOBuffer>)>),
}

impl Supplied<'_> {
  pub fn record(&self) -> &QueryRecord {
    match self {
      Self::Borrowed(record, _) => record,
      Self::Owned(record, _) => record,
      Self::Shared(shared) => &shared.0,
    }
  }

  pub fn io(&self) -> &IOBuffer {
    match self {
      Self::Borrowed(_, io) => io,
      Self::Owned(_, io) => io,
      Self::Shared(shared) => &shared.1,
    }
  }
}

impl AiurSystem {
  pub fn build(
    toplevel: Toplevel,
    commitment_parameters: CommitmentParameters,
    fri_parameters: FriParameters,
  ) -> Self {
    let mut circuit_inputs: Vec<CircuitInputs<G>> = Vec::new();
    let mut slot_widths: Vec<Vec<usize>> = Vec::new();

    let mut push_circuit =
      |main_width: usize,
       preprocessed: Option<RowMajorMatrix<G>>,
       constraints: Vec<Expr<G>>,
       lookups: Vec<Lookup<Expr<G>>>,
       lookup_group_size: usize| {
        slot_widths.push(lookups.iter().map(|l| l.args.len()).collect());
        circuit_inputs.push(CircuitInputs {
          main_width,
          preprocessed,
          constraints,
          ext_constraints: vec![],
          lookups,
          lookup_group_size,
        });
      };

    // Function circuits, in partition order (singletons unless grouped).
    for i in 0..toplevel.circuits.len() {
      let (constraints, lookups) = toplevel.build_constraints(i);
      // A branchless circuit's lookup arguments are sent raw (degree 1;
      // see `ConstraintState::gate`), so two lookups fit in one chained
      // accumulator step at degree 3 — within the degree the selector-gated
      // constraints already pay for. Branching circuits keep k = 1: their
      // superposed arguments are degree 2, and grouping would push the
      // logUp constraints past the quotient budget.
      let group_size =
        if toplevel.circuits[i].layout.selectors == 1 && lookups.len() >= 2 {
          2
        } else {
          1
        };
      push_circuit(
        constraints.width,
        None,
        constraints.zeros,
        lookups,
        group_size,
      );
    }
    // Memories.
    for &size in &toplevel.memory_sizes {
      let (memory, constraints, lookups) = Memory::build(size);
      push_circuit(memory.width, None, constraints, lookups, 1);
    }
    // Gadgets. The byte chips' lookup arguments are preprocessed columns
    // and their multiplicities main columns (all degree 1), so their
    // lookups also group 2 per chained step at degree 3 — halving the
    // stage-2 accumulators (Bytes2: 10 → 5 at height 65536).
    push_circuit(
      Bytes1.main_width(),
      Bytes1.preprocessed(),
      vec![],
      Bytes1.lookups(),
      2,
    );
    push_circuit(
      Bytes2.main_width(),
      Bytes2.preprocessed(),
      vec![],
      Bytes2.lookups(),
      2,
    );

    let config = AiurConfig::new(commitment_parameters, fri_parameters);
    let (system, key) = System::new(config, circuit_inputs);
    AiurSystem {
      system,
      key,
      toplevel,
      commitment_parameters,
      fri_parameters,
      slot_widths,
    }
  }

  /// The circuit list in system order: constrained functions (ascending
  /// index), then memories, then `Bytes1`, then `Bytes2`. This matches the
  /// order the circuits were chained in [`AiurSystem::build`], so index `i`
  /// of the returned `Vec` corresponds to `self.system.circuits[i]`.
  pub fn toplevel(&self) -> &Toplevel {
    &self.toplevel
  }

  pub(crate) fn circuit_types(&self) -> Vec<CircuitType> {
    let functions = (0..self.toplevel.circuits.len())
      .map(|idx| CircuitType::Function { idx });
    let memories = self
      .toplevel
      .memory_sizes
      .iter()
      .map(|&width| CircuitType::Memory { width });
    let gadgets = [CircuitType::Bytes1, CircuitType::Bytes2];
    functions.chain(memories).chain(gadgets).collect()
  }

  /// The argument width of each lookup slot of circuit `circuit_idx`, taken
  /// from the lookups built at construction so the witness layout always
  /// matches the compiled circuit.
  pub(crate) fn slot_arg_widths(&self, circuit_idx: usize) -> Vec<usize> {
    self.slot_widths[circuit_idx].clone()
  }

  /// Per-circuit shape data for the FFT cost model, read straight off the
  /// compiled [`System`] circuits (same order as [`Self::circuit_types`]:
  /// constrained functions ascending, memories, `Bytes1`, `Bytes2`).
  pub fn circuit_shapes(&self) -> Vec<CircuitShape> {
    self
      .system
      .circuits
      .iter()
      .map(|circuit| CircuitShape {
        main_width: circuit.main_width,
        stage2_width: circuit.stage_2_width,
        quotient_degree: circuit.quotient_degree(),
        preprocessed_width: circuit.preprocessed_width,
        preprocessed_height: circuit.preprocessed_height,
      })
      .collect()
  }

  /// Predicted peak prover resident bytes for a record, from circuit
  /// shapes alone — the analytic counterpart of an empirical GiB-per-fft
  /// line. The terms mirror the allocation schedule originally calibrated at
  /// multi-stark rev `2892243e`. The workspace now pins `a8aab731`, so the
  /// model remains useful for relative shard sizing but needs a measured
  /// full-scale re-calibration before its absolute bound is relied upon:
  ///
  /// 1. WITNESS phase: the `QueryRecord` plus every circuit's padded main
  ///    trace and base-field lookup witness, built in parallel and all
  ///    alive at once.
  /// 2. STAGE-2 transition: stage-1 LDEs and their Merkle tree, the
  ///    still-alive lookup witness, the logUp message array plus its
  ///    batch-inverse copy, and the new extension traces.
  /// 3. FRI OPEN: all committed LDEs (main + stage-2 + quotient, at
  ///    `8·2^log_blowup` bytes per trace cell) and their trees, the
  ///    retained FRI fold layers (geometric in `max_log_arity`), and the
  ///    open-phase buffers — all proportional to `H = blowup · tallest`.
  ///
  /// The analytic peak is the max of the three plus the
  /// preprocessed-gadget residency committed at setup. The returned `peak`
  /// additionally applies [`calibrate_prover_rss`] to cover measured
  /// allocator/runtime residency. Heights are `next_power_of_two` of the
  /// record's unique queries — the padding the trace actually commits,
  /// which per-fft models blur.
  pub fn peak_prove_bytes(&self, record: &QueryRecord) -> PeakProveBytes {
    self.peak_prove_bytes_by(
      raw_of(&self.toplevel, record, 1),
      crate::execute::record_retained_bytes(record),
    )
  }

  pub(crate) fn peak_prove_bytes_by(
    &self,
    raw_of: impl Fn(usize, &CircuitType) -> usize,
    record_bytes: usize,
  ) -> PeakProveBytes {
    const S: usize = 8; // bytes per base field element (Goldilocks)
    const DG: usize = 32; // blake3 digest bytes (Merkle nodes, arity 2)
    let b = 1usize << self.commitment_parameters.log_blowup;
    let fold = 1usize << self.fri_parameters.max_log_arity;
    let circuit_types = self.circuit_types();
    let ncirc = self.system.circuits.len();
    let mut tallest = 0usize;
    for (i, ct) in circuit_types.iter().enumerate().take(ncirc) {
      let raw = raw_of(i, ct);
      if raw != 0 {
        tallest = tallest.max(raw.next_power_of_two());
      }
    }
    let mut witness = 0usize;
    let mut s1_lde = 0usize; // stage-1 LDEs
    let mut lookup_w = 0usize; // base-field lookup witness
    let mut msgs = 0usize; // logUp messages (+ inverse copy)
    let mut s2_trace = 0usize; // stage-2 extension traces
    let mut committed = 0usize; // all committed LDE bytes
    let mut prep = 0usize;
    for (i, ct) in circuit_types.iter().enumerate().take(ncirc) {
      let raw = raw_of(i, ct);
      if raw == 0 {
        continue;
      }
      let n = raw.next_power_of_two();
      let c = &self.system.circuits[i];
      let d = EXTENSION_DEGREE;
      let args: usize = self.slot_widths[i].iter().sum();
      let q = c.quotient_degree();
      witness +=
        S * n * c.main_width + S * n * (c.num_lookups + args) + 40 * raw;
      s1_lde += S * b * n * c.main_width;
      lookup_w += S * n * (c.num_lookups + args);
      msgs += 2 * S * d * n * c.num_lookups;
      s2_trace += S * n * c.stage_2_width;
      committed += S * b * n * (c.main_width + c.stage_2_width + q * d);
      prep += S * (1 + b) * c.preprocessed_width * c.preprocessed_height
        + 2 * DG * b * c.preprocessed_height;
    }
    let h = b * tallest;
    let phase_witness = record_bytes + witness;
    let phase_stage2 = s1_lde + 2 * DG * h + lookup_w + msgs + s2_trace;
    // Trees (3 rounds) + retained FRI fold layers + open buffers, all ∝ H.
    let fri_layers = (2 * S + 2 * DG) * h * fold / (fold - 1).max(1);
    let phase_open = committed + 3 * 2 * DG * h + fri_layers + 11 * S * h;
    let analytic_peak = phase_witness.max(phase_stage2).max(phase_open) + prep;
    PeakProveBytes {
      phase_witness,
      phase_stage2,
      phase_open,
      preprocessed: prep,
      retained_stage_1: s1_lde + 2 * DG * h + lookup_w,
      peak: calibrate_prover_rss(analytic_peak),
    }
  }

  /// Smallest power-of-two part count whose projected per-part peak
  /// fits `max_bytes`, assuming the record's rows divide evenly across
  /// parts. The gadget circuits keep their constant heights — they are
  /// the same size in every shard and are most of the model's fixed
  /// floor, which dividing cannot shrink.
  ///
  /// The estimate is optimistic: a part re-executes dependencies shared
  /// across the cut, so its real rows exceed its 1/n share. A caller
  /// splitting on this number must still gate each part on its own
  /// executed record and re-split the ones that miss. Optimism is the
  /// right bias — an under-split costs one cheap re-execution, while an
  /// over-split pays the per-proof floor on every extra part forever.
  ///
  /// Returns 1 when the record already fits.
  pub fn suggested_split_parts(
    &self,
    record: &QueryRecord,
    max_bytes: usize,
  ) -> usize {
    let record_bytes = crate::execute::record_retained_bytes(record);
    let mut parts = 1usize;
    // A shard still over budget at 2^20 parts is not splittable by row
    // count; stop rather than search forever.
    while parts < (1 << 20) {
      let peak = self
        .peak_prove_bytes_by(
          raw_of(&self.toplevel, record, parts),
          record_bytes / parts,
        )
        .peak;
      if peak <= max_bytes {
        break;
      }
      parts *= 2;
    }
    parts
  }

  /// Prove an execution that has ALREADY happened: everything from the
  /// witness phase on, over a record the caller hands across.
  ///
  /// Taking `query_record` by value is the point. The record is the
  /// witness phase's dominant residency, and it is dropped here the
  /// instant the traces exist — before the LDE/commit/FRI phases that
  /// actually set the prover's peak (see [`Self::peak_prove_bytes`]).
  /// A caller that keeps its own copy alive past this call pays that
  /// peak *on top of* the record, which at shard scale is the
  /// difference between fitting in RAM and not.
  ///
  /// `input`, `io_buffer` and `output` must be the ones the execution
  /// ran on: they reconstruct the claim the proof commits to, and the
  /// witness reads the buffer the execution left behind.
  ///
  /// Deliberately not `#[tracing::instrument]`ed — the `aiur/witness`
  /// span below stays directly under the caller's `aiur/prove*` span,
  /// so the stage-scoped measurements keep their existing shape.
  pub fn prove_from_execution(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    io_buffer: &IOBuffer,
    query_record: QueryRecord,
    output: &[G],
  ) -> (Vec<G>, AiurProof) {
    let plan = self.single_shard_plan(&query_record);
    self.prove_from_execution_planned(
      fun_idx,
      input,
      io_buffer,
      query_record,
      output,
      &plan,
      Retention::Retain,
    )
  }

  /// Proves several records as one batch under one claim: the executions of
  /// one statement split across records by deferred calls
  /// ([`crate::execute::Ownership`]), each with its own pointer base. Each
  /// record is planned on its own to `max_cells` and its shards join the
  /// batch in record order; the claim rides on the first shard, and the
  /// closure messages cover every record's memory intervals. The records'
  /// deferred multiplicities must already be absorbed by their owners
  /// ([`QueryRecord::absorb_deferred`]); the witness of every shard is
  /// rebuilt from its record for round two. Fails when a shard exceeds
  /// `max_cells` (a row wider than the budget) or the batch exceeds
  /// [`crate::shard::MAX_SHARDS`], rather than proving what cannot verify.
  pub fn prove_records(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    output: &[G],
    records: &[(QueryRecord, &IOBuffer)],
    max_cells: Option<usize>,
  ) -> Result<(Vec<G>, AiurProof), String> {
    self.prove_record_supplier(
      fun_idx,
      input,
      || output.to_vec(),
      records.len(),
      |r| Ok(Supplied::Borrowed(&records[r].0, records[r].1)),
      max_cells,
    )
  }

  /// [`Self::prove_records`] with the records handed over one at a time:
  /// `supply(r)` is called when record `r` is next in batch order — once
  /// for round one, once for round two — and what it hands over is dropped
  /// when the batch moves on to the next record. A supplier may therefore
  /// execute a record at its first call, keep or recompute it for the
  /// second, and hold at most one record with the prover. The records are
  /// planned as they arrive (nothing about a later record is needed before
  /// an earlier one is committed) and the closure messages are formed once
  /// every record's memory totals are known. The claim's `output` is asked
  /// for when the first shard is committed, after the first record was
  /// supplied, so the execution that produces it need not precede the
  /// batch.
  #[tracing::instrument(level = "info", skip_all, name = "aiur/prove_records")]
  pub fn prove_record_supplier<'a, O, S>(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    output: O,
    count: usize,
    mut supply: S,
    max_cells: Option<usize>,
  ) -> Result<(Vec<G>, AiurProof), String>
  where
    O: FnOnce() -> Vec<G>,
    S: FnMut(usize) -> Result<Supplied<'a>, String>,
  {
    tracing_texray::examine_current();
    if count == 0 {
      return Err("no records to prove".into());
    }
    let mut output = Some(output);
    let mut claim: Option<Vec<G>> = None;
    // Filled by round one as records arrive, read by round two.
    let mut plans: Vec<ShardPlan> = Vec::with_capacity(count);
    let mut indexes: Vec<RowIndex> = Vec::with_capacity(count);
    // Batch shard `k` is local shard `s` of record `r`.
    let mut locate: Vec<(usize, usize)> = Vec::new();
    let mut failure: Option<String> = None;

    // Round one: record by record, shard by shard. The record at hand
    // stays only until its last shard is committed. The stream borrows the
    // state above until the round is over.
    let mut current: Option<(usize, Supplied<'a>, usize)> = None;
    let mut next_record = 0usize;
    let round_one = std::iter::from_fn(|| {
      loop {
        if let Some((r, supplied, shard)) = &mut current {
          let plan = &plans[*r];
          if *shard < plan.num_shards() {
            let s = *shard;
            *shard += 1;
            let claims = if locate.is_empty() {
              let mut formed = vec![function_channel(), G::from_usize(fun_idx)];
              formed.extend(input);
              let output = output.take().expect("the output is asked once");
              formed.extend(output());
              claim = Some(formed.clone());
              vec![formed]
            } else {
              vec![]
            };
            locate.push((*r, s));
            let _g = tracing::info_span!("aiur/witness").entered();
            let witness = self.shard_witness(
              supplied.record(),
              supplied.io(),
              plan,
              &indexes[*r],
              s,
            );
            return Some((claims, witness));
          }
          current = None;
        }
        if next_record == count {
          return None;
        }
        let r = next_record;
        next_record += 1;
        let supplied = match supply(r) {
          Ok(supplied) => supplied,
          Err(error) => {
            failure = Some(format!("record {r}: {error}"));
            return None;
          },
        };
        let plan = self.plan_shards(supplied.record(), max_cells);
        if locate.len() + plan.num_shards() > crate::shard::MAX_SHARDS {
          failure =
            Some(format!("record {r}: the batch exceeds the shard limit"));
          return None;
        }
        if let Some(max_cells) = max_cells {
          let heaviest = self.shard_committed_cells(&plan).into_iter().max();
          if let Some(cells) = heaviest.filter(|&cells| cells > max_cells) {
            failure = Some(format!(
              "record {r}: a shard of {cells} committed cells exceeds the \
               budget of {max_cells}"
            ));
            return None;
          }
        }
        eprintln!("[distributed] record {r}: {} shards", plan.num_shards());
        indexes.push(self.row_index(supplied.record(), &plan));
        plans.push(plan);
        current = Some((r, supplied, 0));
      }
    });
    let barrier = self.system.batch_round_one(round_one, Retention::Regenerate);
    if let Some(error) = failure {
      return Err(error);
    }
    let claim = claim.ok_or("no shards to prove")?;
    let mut memory_totals: Vec<(usize, usize, usize)> = plans
      .iter()
      .flat_map(|plan| plan.memory_totals.iter().copied())
      .collect();
    memory_totals.sort_unstable();
    let messages =
      Self::boundary_messages(&ShardPlan { shards: vec![], memory_totals });

    // Round two: the record is asked for again when the batch order
    // reaches it and dropped when the order moves on.
    let mut loaded: Option<(usize, Supplied<'a>)> = None;
    let proof =
      self.system.batch_round_two(&self.key, barrier, messages, |k| {
        let (r, s) = locate[k];
        if loaded.as_ref().is_none_or(|(at, _)| *at != r) {
          loaded = None;
          let supplied =
            supply(r).unwrap_or_else(|error| panic!("record {r}: {error}"));
          loaded = Some((r, supplied));
        }
        let supplied = &loaded.as_ref().expect("loaded above").1;
        let _g = tracing::info_span!("aiur/witness").entered();
        self.shard_witness(
          supplied.record(),
          supplied.io(),
          &plans[r],
          &indexes[r],
          s,
        )
      });
    Ok((claim, proof))
  }

  /// [`Self::prove_from_execution`] with the record's rows dealt out to the
  /// fewest shards whose committed cells each fit `max_cells`
  /// ([`Self::plan_shards`]). With more than one shard, only the headers
  /// survive the batch barrier and each shard is rebuilt from the record
  /// for round two ([`Retention::Regenerate`]), so the peak is the record
  /// plus one shard rather than the stage-1 state of every shard. A plan
  /// of one shard has nothing to save and is proven as the unsharded
  /// execution is ([`Retention::Retain`]).
  pub fn prove_from_execution_sharded(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    io_buffer: &IOBuffer,
    query_record: QueryRecord,
    output: &[G],
    max_cells: usize,
  ) -> (Vec<G>, AiurProof) {
    let plan = self.plan_shards(&query_record, Some(max_cells));
    let retention = if plan.num_shards() == 1 {
      Retention::Retain
    } else {
      Retention::Regenerate
    };
    self.prove_from_execution_planned(
      fun_idx,
      input,
      io_buffer,
      query_record,
      output,
      &plan,
      retention,
    )
  }

  /// Proves an execution as the batch of trace shards `plan` describes: one
  /// witness per shard, the claim in shard 0, and the `memseg` closure
  /// messages for the plan's memory totals.
  ///
  /// Under [`Retention::Retain`] every shard's witness is built first and
  /// the record is released before proving starts, so the record and the
  /// proving state never coexist, but the whole batch's stage 1 does. Under
  /// [`Retention::Regenerate`] the record stays until the last shard is
  /// proven and each shard's witness is built from it when needed, twice.
  pub fn prove_from_execution_planned(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    io_buffer: &IOBuffer,
    query_record: QueryRecord,
    output: &[G],
    plan: &ShardPlan,
    retention: Retention,
  ) -> (Vec<G>, AiurProof) {
    // Construct the claim.
    let mut claim = vec![function_channel(), G::from_usize(fun_idx)];
    claim.extend(input);
    claim.extend(output);

    let claims: Vec<Vec<Vec<G>>> = (0..plan.num_shards())
      .map(|shard| if shard == 0 { vec![claim.clone()] } else { vec![] })
      .collect();
    let messages = Self::boundary_messages(plan);
    let index = self.row_index(&query_record, plan);
    let build = |shard: usize| {
      let _g = tracing::info_span!("aiur/witness").entered();
      self.shard_witness(&query_record, io_buffer, plan, &index, shard)
    };
    let proof = match retention {
      Retention::Retain => {
        let mut witnesses: Vec<_> =
          (0..plan.num_shards()).map(|shard| Some(build(shard))).collect();
        drop(query_record);
        self.system.prove_batch_with(
          &self.key,
          &claims,
          messages,
          Retention::Retain,
          |shard| witnesses[shard].take().expect("each shard is built once"),
        )
      },
      Retention::Regenerate => self.system.prove_batch_with(
        &self.key,
        &claims,
        messages,
        Retention::Regenerate,
        build,
      ),
    };
    (claim, proof)
  }

  #[tracing::instrument(level = "info", skip_all, name = "aiur/prove")]
  pub fn prove(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    io_buffer: &mut IOBuffer,
  ) -> (Vec<G>, AiurProof) {
    tracing_texray::examine_current();

    // Execute the Aiur bytecode.
    let _g = tracing::info_span!("aiur/execute").entered();
    // Execute the Aiur bytecode. The prover assumes inputs are valid; any
    // execution error here is a programmer bug, so we unwrap.
    let (query_record, output) = self
      .toplevel
      .execute(fun_idx, input.to_vec(), io_buffer)
      .expect("Aiur execution failed during prove");
    drop(_g);

    self.prove_from_execution(fun_idx, input, io_buffer, query_record, &output)
  }

  /// IxVM-native prove: identical to `prove` except the execute step
  /// is provided by the caller as `executor` (a closure that runs
  /// the codegen'd Rust kernel `ix::aiur_ixvm_runner::execute_ixvm`
  /// instead of the bytecode interpreter). Avoids a circular crate
  /// dependency: `aiur` doesn't know about `ix`; `ix` (or its
  /// downstream `ffi`) injects the executor.
  ///
  /// QueryRecord shape + witness construction + claim layout + proof
  /// generation are all unchanged — the proof produced here is
  /// verification-compatible with one produced by `prove`.
  #[tracing::instrument(level = "info", skip_all, name = "aiur/prove_ixvm")]
  pub fn prove_ixvm<F>(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    io_buffer: &mut IOBuffer,
    executor: F,
  ) -> (Vec<G>, AiurProof)
  where
    F: FnOnce(
      &Toplevel,
      FunIdx,
      Vec<G>,
      &mut IOBuffer,
    ) -> Result<(QueryRecord, Vec<G>), ExecError>,
  {
    match self.prove_ixvm_within_budget(
      fun_idx, input, io_buffer, executor, None, false, false, None,
    ) {
      GatedProve::Proved { claim, proof, .. } => (claim, proof),
      _ => unreachable!("an unbudgeted prove always proves"),
    }
  }

  /// `prove_ixvm`, but the record's projected prover peak has to fit
  /// `max_bytes` before any proving starts (`None` skips the check),
  /// and `exec_only` stops after execution + measurement — the split
  /// loop runs on executions alone, no STARK started.
  ///
  /// The peak is measured on the REAL record ([`Self::peak_prove_bytes`]),
  /// not estimated from serialized bytes, so an over-budget shard is
  /// caught in the gap between execution and the witness phase — before
  /// the LDE/commit/FRI phases that would actually exhaust the box. With
  /// `trace_shards`, an over-budget record is first planned as trace
  /// shards ([`Self::plan_shards_within`]) and, if some shard count fits,
  /// proven as that batch with the record resident throughout; the peak
  /// reported is then the heaviest shard's projection. Otherwise — or
  /// without `trace_shards` — the record is dropped and
  /// [`GatedProve::Split`] carries the part count
  /// [`Self::suggested_split_parts`] projects will fit, computed here
  /// because this is the last moment the record exists to read counts
  /// from. Every outcome carries the measured peak: proving a shard
  /// measures it for free, so a prove run yields the same split/merge
  /// signal a check run does without a second execution.
  #[tracing::instrument(
    level = "info",
    skip_all,
    name = "aiur/prove_ixvm_within_budget"
  )]
  pub fn prove_ixvm_within_budget<F>(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    io_buffer: &mut IOBuffer,
    executor: F,
    max_bytes: Option<usize>,
    exec_only: bool,
    trace_shards: bool,
    retention: Option<Retention>,
  ) -> GatedProve
  where
    F: FnOnce(
      &Toplevel,
      FunIdx,
      Vec<G>,
      &mut IOBuffer,
    ) -> Result<(QueryRecord, Vec<G>), ExecError>,
  {
    tracing_texray::examine_current();
    let _g = tracing::info_span!("aiur/execute_ixvm").entered();
    let (query_record, output) =
      executor(&self.toplevel, fun_idx, input.to_vec(), io_buffer)
        .expect("IxVM-native Aiur execution failed during prove_ixvm");
    drop(_g);

    let peak = self.peak_prove_bytes(&query_record).peak;
    if let Some(max) = max_bytes
      && peak > max
    {
      if trace_shards {
        let record_bytes = crate::execute::record_retained_bytes(&query_record);
        // `AIUR_TRACE_SHARD_MAX_CELLS` plans to a committed-cell budget
        // (a device-residency bound, e.g. VRAM) instead of the host peak.
        let planned = match std::env::var("AIUR_TRACE_SHARD_MAX_CELLS")
          .ok()
          .and_then(|v| v.parse::<usize>().ok())
        {
          Some(cells) => {
            let plan = self.plan_shards(&query_record, Some(cells));
            let shard_peak = (0..plan.num_shards())
              .map(|s| self.shard_peak_bytes(&plan, s, record_bytes))
              .max()
              .unwrap_or(0);
            Ok((plan, shard_peak))
          },
          None => self.plan_shards_within(&query_record, max),
        };
        match planned {
          Ok((plan, shard_peak)) => {
            let retention = retention
              .unwrap_or_else(|| self.retention_for(&plan, record_bytes, max));
            eprintln!(
              "[trace-shards] {} shards for a {} B budget: record {} B, \
               whole-execution peak {} B, heaviest shard peak {} B, {}",
              plan.num_shards(),
              max,
              record_bytes,
              peak,
              shard_peak,
              match retention {
                Retention::Retain => "retaining every shard's stage 1",
                Retention::Regenerate => "regenerating each shard for round 2",
              }
            );
            // Per-circuit committed widths, so a plan's padded cells and
            // active width can be computed from the row ranges below.
            let widths: Vec<String> =
              self.committed_widths().iter().map(usize::to_string).collect();
            eprintln!("[trace-shards] committed widths: {}", widths.join(" "));
            for (shard, rows) in plan.shards.iter().enumerate() {
              let ranges: Vec<String> = rows
                .rows
                .iter()
                .enumerate()
                .filter(|(_, r)| !r.is_empty())
                .map(|(ci, r)| format!("{ci}:{}..{}", r.start, r.end))
                .collect();
              eprintln!(
                "[trace-shards] shard {shard}: projected peak {} B, rows {}",
                self.shard_peak_bytes(&plan, shard, record_bytes),
                ranges.join(" ")
              );
            }
            if exec_only {
              return GatedProve::Measured { peak: shard_peak };
            }
            let (claim, proof) = self.prove_from_execution_planned(
              fun_idx,
              input,
              io_buffer,
              query_record,
              &output,
              &plan,
              retention,
            );
            return GatedProve::Proved { claim, proof, peak: shard_peak };
          },
          Err(floor) => eprintln!(
            "[trace-shards] no shard count fits a {} B budget: record {} B, \
             whole-execution peak {} B, lowest heaviest-shard peak {} B",
            max, record_bytes, peak, floor
          ),
        }
      }
      let parts = self.suggested_split_parts(&query_record, max);
      return GatedProve::Split { peak, parts };
    }
    if exec_only {
      return GatedProve::Measured { peak };
    }
    let (claim, proof) = self.prove_from_execution(
      fun_idx,
      input,
      io_buffer,
      query_record,
      &output,
    );
    GatedProve::Proved { claim, proof, peak }
  }

  /// Verifies a proof of `claim`: Aiur's batch policy (one claim, canonical
  /// `memseg` closure — see [`crate::shard`]), then the multi-stark batch.
  pub fn verify(
    &self,
    claim: &[G],
    proof: &AiurProof,
  ) -> Result<(), AiurVerificationError> {
    self
      .check_batch_policy(claim, &proof.preamble)
      .map_err(AiurVerificationError::Policy)?;
    self.system.verify_batch(proof)?;
    Ok(())
  }

  /// Verify and serialize the native Plonky3 multiproof for the in-circuit
  /// recursive verifier.
  pub fn proof_to_advice_bytes(
    &self,
    claim: &[G],
    proof: &AiurProof,
  ) -> Result<Vec<u8>, String> {
    self.verify(claim, proof).map_err(|e| format!("{e:?}"))?;
    proof.to_bytes().map_err(|e| format!("{e:?}"))
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::{
    bytecode::{Block, Ctrl, Function, FunctionLayout, Op, Toplevel},
    execute::{IOBuffer, Ownership, pointer_stride},
    shard::ShardRows,
  };
  use multi_stark::{
    batch::ShardInput,
    lookup::LookupValues,
    p3_field::PrimeCharacteristicRing,
    system::SystemWitness,
    types::{CommitmentParameters, FriParameters},
  };
  use rustc_hash::FxHashMap;

  /// A grouped circuit's raw rows are the sum over its members — the peak
  /// model must not read one function's entries by circuit index.
  #[test]
  fn grouped_circuit_rows_sum_their_members() {
    let mut toplevel = call_and_memory_toplevel();
    let layout = toplevel.circuits[0].layout;
    toplevel.circuits =
      vec![crate::bytecode::Circuit { members: vec![0, 1], layout }];
    let mut io_buffer = empty_io_buffer();
    let (record, _) = toplevel
      .execute(0, vec![G::from_u64(3), G::from_u64(5)], &mut io_buffer)
      .expect("f(3, 5) executes");
    let f_rows = record.function_queries[0].len();
    let g_rows = record.function_queries[1].len();
    assert!(f_rows > 0 && g_rows > 0);
    let grouped = CircuitType::Function { idx: 0 };
    assert_eq!(raw_of(&toplevel, &record, 1)(0, &grouped), f_rows + g_rows);
    assert_eq!(
      raw_of(&toplevel, &record, 2)(0, &grouped),
      (f_rows + g_rows).div_ceil(2)
    );
  }

  #[test]
  fn prover_rss_calibration_rounds_up_and_saturates() {
    assert_eq!(calibrate_prover_rss(40), 43);
    assert_eq!(calibrate_prover_rss(1_000), 1_075);
    assert_eq!(calibrate_prover_rss(usize::MAX), usize::MAX);
  }

  /// Small FRI parameters mirroring `vk_codec`'s test config: cheap to prove
  /// while still exercising the full FRI pipeline (log_blowup 1, 64 queries,
  /// no proof-of-work).
  fn test_parameters() -> (CommitmentParameters, FriParameters) {
    let cp = CommitmentParameters { log_blowup: 1, cap_height: 0 };
    let fp = FriParameters {
      log_final_poly_len: 0,
      max_log_arity: 1,
      num_queries: 64,
      commit_proof_of_work_bits: 0,
      query_proof_of_work_bits: 0,
    };
    (cp, fp)
  }

  fn empty_io_buffer() -> IOBuffer {
    IOBuffer { data: FxHashMap::default(), map: FxHashMap::default() }
  }

  /// Hand-build the toplevel for a single constrained function `f(a, b) = a*b`.
  ///
  /// Body: `Mul(0, 1)` (multiplies the two inputs, which live at value indices
  /// 0 and 1, producing value index 2), then `Return(0, [2])`.
  ///
  /// Layout — matched against how `constraints.rs`/`trace.rs` walk the block:
  /// - `input_size = 2`: the two inputs `a`, `b`.
  /// - `selectors = 1`: the single `Return` (selector index 0).
  /// - `auxiliaries = 2`: the multiplicity column (allocated first for every
  ///   function) plus one auxiliary for the `Mul` — `a` and `b` each have
  ///   degree 1, so `a*b` has degree 2 and `constraints.rs` spills it into a
  ///   fresh auxiliary column pinned by `sel * (col - a*b)`.
  /// - `lookups = 1`: the function-provide (return) lookup in slot 0, which
  ///   pulls the claim `[function_channel, fun_idx, a, b, a*b]`.
  ///
  /// Test-side singleton partition (production circuits come pre-built from
  /// the Lean compiler).
  fn with_singleton_circuits(
    functions: Vec<Function>,
    memory_sizes: Vec<usize>,
  ) -> Toplevel {
    let circuits = functions
      .iter()
      .enumerate()
      .filter(|(_, f)| f.constrained)
      .map(|(i, f)| crate::bytecode::Circuit {
        members: vec![i],
        layout: f.layout,
      })
      .collect();
    Toplevel { functions, memory_sizes, circuits }
  }

  fn mul_toplevel() -> Toplevel {
    let body =
      Block { ops: vec![Op::Mul(0, 1)], ctrl: Ctrl::Return(0, vec![2]) };
    let function = Function {
      body,
      layout: FunctionLayout {
        input_size: 2,
        selectors: 1,
        auxiliaries: 2,
        lookups: 1,
      },
      entry: true,
      constrained: true,
    };
    with_singleton_circuits(vec![function], vec![])
  }

  fn xor_splits_toplevel() -> Toplevel {
    let body = Block {
      ops: vec![Op::U8XorSplit7(0, 1), Op::U8XorSplit4(0, 1)],
      ctrl: Ctrl::Return(0, vec![2, 3, 4, 5]),
    };
    let function = Function {
      body,
      layout: FunctionLayout {
        input_size: 2,
        selectors: 1,
        auxiliaries: 5,
        lookups: 3,
      },
      entry: true,
      constrained: true,
    };
    with_singleton_circuits(vec![function], vec![])
  }

  #[test]
  fn prove_verify_xor_splits() {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(xor_splits_toplevel(), cp, fp);
    let input = [G::from_u8(0xd3), G::from_u8(0x69)];
    let mut io_buffer = empty_io_buffer();

    let (claim, proof) = system.prove(0, &input, &mut io_buffer);
    let (s7_hi, s7_lo) = Bytes2::xor_split7(&input[0], &input[1]);
    let (s4_hi, s4_lo) = Bytes2::xor_split4(&input[0], &input[1]);
    assert_eq!(
      claim,
      vec![
        function_channel(),
        G::ZERO,
        input[0],
        input[1],
        s7_hi,
        s7_lo,
        s4_hi,
        s4_lo,
      ]
    );
    system.verify(&claim, &proof).expect("xor split outputs must verify");
  }

  /// Hand-build a toplevel exercising the two migrated integration paths that
  /// the `Mul` test does not: the cross-circuit **function-channel** lookup (a
  /// function calling another) and the **memory circuit** (a `Store` followed
  /// by a `Load`, which adds a `Memory` circuit and proves its migrated
  /// transition + memory-channel-lookup constraints).
  ///
  /// Functions:
  /// - `f` (idx 0, entry): `f(a, b) = g(a) * b`, but routing `b` through
  ///   memory so the memory path is live:
  ///   - `Call(1, [a], 1, false)` → `g(a)` at value idx 2, allocating one
  ///     output auxiliary + one function-channel lookup slot.
  ///   - `Store([b])` → pointer at value idx 3, allocating one pointer
  ///     auxiliary + one memory-channel lookup slot (multiplicity pushed).
  ///   - `Load(1, 3)` → the loaded `b` at value idx 4, allocating one value
  ///     auxiliary + one memory-channel lookup slot.
  ///   - `Mul(2, 4)` → `g(a) * b` (both degree 1 ⇒ degree 2 ⇒ spilled into a
  ///     fresh auxiliary at value idx 5).
  ///   - `Return(0, [5])`.
  ///
  ///   Layout for `f` — matched against how `constraints.rs`/`trace.rs` walk
  ///   the block:
  ///   - `input_size = 2` (`a`, `b`).
  ///   - `selectors = 1` (the single `Return`).
  ///   - `auxiliaries = 5`: multiplicity(1) + call output(1) + store ptr(1) +
  ///     load value(1) + mul spill(1).
  ///   - `lookups = 4`: return(slot 0) + call(1) + store(1) + load(1).
  ///
  /// - `g` (idx 1): `g(x) = x + 1`:
  ///   - `Const(1)` at value idx 1, `Add(0, 1)` at value idx 2,
  ///     `Return(0, [2])`. `Const`/`Add` allocate no auxiliaries.
  ///   - Layout: `input_size = 1`, `selectors = 1`, `auxiliaries = 1`
  ///     (multiplicity only), `lookups = 1` (return only).
  ///
  /// `memory_sizes = [1]`: a memory of size-1 values, which materializes one
  /// `Memory` circuit. The single `Store` inserts the entry (memory
  /// multiplicity 1); the `Load` bumps it to 2. The function circuit pushes
  /// `+1` for the store lookup and `+1` for the load lookup; the memory circuit
  /// pulls `-2`. The whole system balances across the function↔function and
  /// function↔memory channels.
  fn call_and_memory_toplevel() -> Toplevel {
    let f_body = Block {
      ops: vec![
        Op::Call(1, vec![0], 1, false),
        Op::Store(vec![1]),
        Op::Load(1, 3),
        Op::Mul(2, 4),
      ],
      ctrl: Ctrl::Return(0, vec![5]),
    };
    let f = Function {
      body: f_body,
      layout: FunctionLayout {
        input_size: 2,
        selectors: 1,
        auxiliaries: 5,
        lookups: 4,
      },
      entry: true,
      constrained: true,
    };

    let g_body = Block {
      ops: vec![Op::Const(G::ONE), Op::Add(0, 1)],
      ctrl: Ctrl::Return(0, vec![2]),
    };
    let g = Function {
      body: g_body,
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 1,
        lookups: 1,
      },
      entry: false,
      constrained: true,
    };

    with_singleton_circuits(vec![f, g], vec![1])
  }

  #[test]
  fn prove_verify_call_and_memory_roundtrip() {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(call_and_memory_toplevel(), cp, fp);

    let a = G::from_u64(3);
    let b = G::from_u64(5);
    let input = [a, b];
    let mut io_buffer = empty_io_buffer();

    // f(a, b) = g(a) * b = (a + 1) * b, with b routed through a Store/Load.
    let expected = (a + G::ONE) * b;
    let (claim, proof) = system.prove(0, &input, &mut io_buffer);

    // Claim layout is [function_channel(), fun_idx, input.., output..].
    assert_eq!(
      claim,
      vec![function_channel(), G::from_usize(0), a, b, expected],
      "unexpected claim layout / computed output"
    );

    system
      .verify(&claim, &proof)
      .expect("valid proof over Call + Store/Load must verify");

    // Negative check: tampering with the output element must make the claim
    // inconsistent with the (honest) proof, so verification must fail.
    let mut bad_claim = claim.clone();
    let last = bad_claim.len() - 1;
    bad_claim[last] += G::ONE;
    assert!(
      system.verify(&bad_claim, &proof).is_err(),
      "verification must reject a tampered claim"
    );
  }

  /// Exercise promotion of a cached unconstrained call through nested calls.
  ///
  /// `f` first computes `g(x)` as an unconstrained hint, then calls `g(x)`
  /// constrained.  Since `g` calls `h`, promoting the cached `g` query must
  /// replay its body and promote the cached `h` query as well.  Merely bumping
  /// `g`'s multiplicity leaves the `g -> h` function channel unbalanced.
  fn unconstrained_call_promotion_toplevel() -> Toplevel {
    let f = Function {
      body: Block {
        ops: vec![
          Op::Call(1, vec![0], 1, true),
          Op::Call(1, vec![0], 1, false),
        ],
        ctrl: Ctrl::Return(0, vec![2]),
      },
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 3,
        lookups: 2,
      },
      entry: true,
      constrained: true,
    };

    let g = Function {
      body: Block {
        ops: vec![Op::Call(2, vec![0], 1, false)],
        ctrl: Ctrl::Return(0, vec![1]),
      },
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 2,
        lookups: 2,
      },
      entry: false,
      constrained: true,
    };

    let h = Function {
      body: Block {
        ops: vec![Op::Const(G::ONE), Op::Add(0, 1)],
        ctrl: Ctrl::Return(0, vec![2]),
      },
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 1,
        lookups: 1,
      },
      entry: false,
      constrained: true,
    };

    with_singleton_circuits(vec![f, g, h], vec![])
  }

  #[test]
  fn prove_verify_promotes_nested_unconstrained_call() {
    let (cp, fp) = test_parameters();
    let system =
      AiurSystem::build(unconstrained_call_promotion_toplevel(), cp, fp);
    let input = [G::from_u64(3)];
    let mut io_buffer = empty_io_buffer();

    let (claim, proof) = system.prove(0, &input, &mut io_buffer);
    assert_eq!(
      claim,
      vec![function_channel(), G::ZERO, input[0], input[0] + G::ONE]
    );
    system
      .verify(&claim, &proof)
      .expect("nested constrained promotion must balance function channels");
  }

  #[test]
  fn prove_verify_mul_roundtrip() {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(mul_toplevel(), cp, fp);

    let a = G::from_u64(3);
    let b = G::from_u64(5);
    let input = [a, b];
    let mut io_buffer = empty_io_buffer();

    let (claim, proof) = system.prove(0, &input, &mut io_buffer);

    // Claim layout is [function_channel(), fun_idx, input.., output..].
    assert_eq!(
      claim,
      vec![function_channel(), G::from_usize(0), a, b, a * b],
      "unexpected claim layout / computed output"
    );

    system.verify(&claim, &proof).expect("valid proof must verify");

    // Negative check: tampering with the output element must make the claim
    // inconsistent with the (honest) proof, so verification must fail.
    let mut bad_claim = claim.clone();
    let last = bad_claim.len() - 1;
    bad_claim[last] += G::ONE;
    assert!(
      system.verify(&bad_claim, &proof).is_err(),
      "verification must reject a tampered claim"
    );
  }

  #[test]
  fn circuit_shapes_match_system() {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(call_and_memory_toplevel(), cp, fp);
    let shapes = system.circuit_shapes();

    // Canonical order and count: 2 constrained functions, 1 memory, Bytes1,
    // Bytes2.
    assert_eq!(shapes.len(), 5);
    assert_eq!(shapes.len(), system.system.circuits.len());

    for (shape, circuit) in shapes.iter().zip(&system.system.circuits) {
      assert_eq!(shape.main_width, circuit.main_width);
      assert_eq!(shape.stage2_width, circuit.stage_2_width);
      assert_eq!(shape.quotient_degree, circuit.quotient_degree());
      assert_eq!(shape.preprocessed_width, circuit.preprocessed_width);
      assert_eq!(shape.preprocessed_height, circuit.preprocessed_height);
    }

    // Function circuits: main width = inputs + selectors + auxiliaries, no
    // preprocessed matrix.
    assert_eq!(shapes[0].main_width, 2 + 1 + 5);
    assert_eq!(shapes[1].main_width, 1 + 1 + 1);
    // Memory of size 1: multiplicity + selector + pointer + 1 value.
    assert_eq!(shapes[2].main_width, 3 + 1);
    for shape in &shapes[..3] {
      assert_eq!(shape.preprocessed_width, 0);
      assert_eq!(shape.preprocessed_height, 0);
    }

    // Byte gadgets: always-active fixed-height tables whose preprocessed
    // height doubles as the committed trace height.
    assert_eq!(shapes[3].preprocessed_width, 11);
    assert_eq!(shapes[3].preprocessed_height, 256);
    assert_eq!(shapes[4].preprocessed_width, 14);
    assert_eq!(shapes[4].preprocessed_height, 65536);
  }

  // -- Trace shards --
  //
  // `call_and_memory_toplevel`'s system order: f, g, memory[1], Bytes1,
  // Bytes2. Its record has one row of f, one of g, and one memory row.
  const F: usize = 0;
  const G_FN: usize = 1;
  const MEM: usize = 2;
  const BYTES1: usize = 3;
  const BYTES2: usize = 4;

  fn executed_call_and_memory()
  -> (AiurSystem, Vec<G>, QueryRecord, Vec<G>, IOBuffer) {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(call_and_memory_toplevel(), cp, fp);
    let input = vec![G::from_u64(3), G::from_u64(5)];
    let mut io_buffer = empty_io_buffer();
    let (record, output) = system
      .toplevel()
      .execute(0, input.clone(), &mut io_buffer)
      .expect("execution succeeds");
    (system, input, record, output, io_buffer)
  }

  /// Two shards: `f` and the byte tables in shard 0, `g` in shard 1, and the
  /// memory row wherever `memory_ranges` puts it (one range per shard).
  fn two_shard_plan(memory_ranges: [std::ops::Range<usize>; 2]) -> ShardPlan {
    let mut shard_0 = vec![0..0; 5];
    let mut shard_1 = vec![0..0; 5];
    shard_0[F] = 0..1;
    shard_0[BYTES1] = 0..256;
    shard_0[BYTES2] = 0..65536;
    shard_1[G_FN] = 0..1;
    let [range_0, range_1] = memory_ranges;
    shard_0[MEM] = range_0;
    shard_1[MEM] = range_1;
    ShardPlan {
      shards: vec![ShardRows { rows: shard_0 }, ShardRows { rows: shard_1 }],
      memory_totals: vec![(1, 0, 1)],
    }
  }

  #[test]
  fn sharded_prove_verify_across_two_shards() {
    let (system, input, record, output, io_buffer) = executed_call_and_memory();
    // The memory table lives in the shard WITHOUT the claim and WITHOUT the
    // caller's store/load rows: every memory message crosses the cut.
    let plan = two_shard_plan([0..0, 0..1]);
    let (claim, proof) = system.prove_from_execution_planned(
      0,
      &input,
      &io_buffer,
      record,
      &output,
      &plan,
      Retention::Regenerate,
    );
    assert_eq!(proof.proofs.len(), 2);
    // The byte tables are present in both shards; only shard 0's copy
    // carries multiplicities.
    assert!(proof.proofs[0].active[BYTES1] && proof.proofs[0].active[BYTES2]);
    assert!(proof.proofs[1].active[BYTES1] && proof.proofs[1].active[BYTES2]);
    assert!(!proof.proofs[0].active[MEM] && proof.proofs[1].active[MEM]);
    assert_eq!(proof.preamble.headers[0].claims.len(), 1);
    assert!(proof.preamble.headers[1].claims.is_empty());
    system.verify(&claim, &proof).expect("two-shard proof verifies");

    let mut bad_claim = claim.clone();
    let last = bad_claim.len() - 1;
    bad_claim[last] += G::ONE;
    assert!(matches!(
      system.verify(&bad_claim, &proof),
      Err(AiurVerificationError::Policy(_))
    ));
  }

  #[test]
  fn sharded_proof_bytes_round_trip() {
    let (system, input, record, output, io_buffer) = executed_call_and_memory();
    let plan = two_shard_plan([0..1, 0..0]);
    let (claim, proof) = system.prove_from_execution_planned(
      0,
      &input,
      &io_buffer,
      record,
      &output,
      &plan,
      Retention::Retain,
    );
    let bytes = proof.to_bytes().expect("serialize");
    let decoded = AiurProof::from_bytes(&bytes).expect("deserialize");
    system.verify(&claim, &decoded).expect("decoded proof verifies");
  }

  #[test]
  fn plan_shards_respects_budget_and_covers_every_row() {
    let (system, input, record, output, io_buffer) = executed_call_and_memory();
    let single = system.single_shard_plan(&record);
    assert_eq!(single.num_shards(), 1);
    assert_eq!(single.memory_totals, vec![(1, 0, 1)]);

    // Every committed cell of the single shard, less one, forces a second
    // shard; the byte tables stay in shard 0 and everything else moves.
    let widths: Vec<usize> = system
      .circuit_shapes()
      .iter()
      .map(|s| {
        s.main_width + s.stage2_width + s.quotient_degree * EXTENSION_DEGREE
      })
      .collect();
    // Every shard commits the byte tables, so they are charged to each.
    let cells = |plan: &ShardPlan, shard: usize| -> usize {
      plan.shards[shard]
        .rows
        .iter()
        .zip(&widths)
        .zip(&single.shards[0].rows)
        .enumerate()
        .map(|(ci, ((r, &w), whole))| {
          let r = if ci == BYTES1 || ci == BYTES2 { whole } else { r };
          if r.is_empty() { 0 } else { r.len().next_power_of_two() * w }
        })
        .sum()
    };
    let total = cells(&single, 0);
    let plan = system.plan_shards(&record, Some(total - 1));
    assert_eq!(plan.num_shards(), 2);
    assert!(cells(&plan, 0) < total && cells(&plan, 1) < total);
    for ci in 0..5 {
      let covered: usize = plan.shards.iter().map(|s| s.rows[ci].len()).sum();
      assert_eq!(covered, single.shards[0].rows[ci].len(), "circuit {ci}");
    }
    assert_eq!(plan.shards[0].rows[BYTES2], 0..65536);
    assert!(plan.shards[1].rows[BYTES2].is_empty());

    // A budget nothing can meet still yields a plan (the byte tables floor
    // shard 0), without searching further than the three placeable rows
    // allow.
    let floored = system.plan_shards(&record, Some(1));
    assert!((1..=3).contains(&floored.num_shards()));
    for ci in 0..5 {
      let covered: usize =
        floored.shards.iter().map(|s| s.rows[ci].len()).sum();
      assert_eq!(covered, single.shards[0].rows[ci].len(), "circuit {ci}");
    }

    let (claim, proof) = system.prove_from_execution_planned(
      0,
      &input,
      &io_buffer,
      record,
      &output,
      &plan,
      Retention::Retain,
    );
    system.verify(&claim, &proof).expect("planned two-shard proof verifies");
  }

  #[test]
  fn rejects_duplicated_memory_range() {
    let (system, input, record, output, io_buffer) = executed_call_and_memory();
    // Both shards claim pointer 0: two `0 → 1` edges against one boot and
    // one terminal term.
    let plan = two_shard_plan([0..1, 0..1]);
    let (claim, proof) = system.prove_from_execution_planned(
      0,
      &input,
      &io_buffer,
      record,
      &output,
      &plan,
      Retention::Retain,
    );
    assert!(matches!(
      system.verify(&claim, &proof),
      Err(AiurVerificationError::Stark(VerificationError::UnbalancedBatch))
    ));
  }

  #[test]
  fn rejects_memory_row_missing_from_every_shard() {
    let (system, input, record, output, io_buffer) = executed_call_and_memory();
    // No shard carries the memory table, yet the plan still closes it: the
    // closure's end points (0 and 1) then match no rows, and the caller's
    // store/load pushes match no pull.
    let plan = two_shard_plan([0..0, 0..0]);
    let (claim, proof) = system.prove_from_execution_planned(
      0,
      &input,
      &io_buffer,
      record,
      &output,
      &plan,
      Retention::Retain,
    );
    assert!(matches!(
      system.verify(&claim, &proof),
      Err(AiurVerificationError::Stark(VerificationError::UnbalancedBatch))
    ));
  }

  #[test]
  fn rejects_overlapping_closure_intervals() {
    let (system, input, record, output, io_buffer) = executed_call_and_memory();
    // Both shards hold pointer 0 of width 1, and the plan closes `[0, 1)`
    // twice: balanced as a sum, rejected as a policy violation.
    let mut plan = two_shard_plan([0..1, 0..1]);
    plan.memory_totals.push((1, 0, 1));
    let (claim, proof) = system.prove_from_execution_planned(
      0,
      &input,
      &io_buffer,
      record,
      &output,
      &plan,
      Retention::Retain,
    );
    assert!(matches!(
      system.verify(&claim, &proof),
      Err(AiurVerificationError::Policy(_))
    ));
  }

  /// `f(a)` (entry) calls `h(a)`, which returns nothing: it stores `a`,
  /// loads it back and asserts the round trip. `h` is an entry too, so a
  /// record that owns it can run it directly.
  fn deferral_toplevel() -> Toplevel {
    let f = Function {
      body: Block {
        ops: vec![Op::Call(1, vec![0], 0, false)],
        ctrl: Ctrl::Return(0, vec![0]),
      },
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 1,
        lookups: 2,
      },
      entry: true,
      constrained: true,
    };
    let h = Function {
      body: Block {
        ops: vec![
          Op::Store(vec![0]),
          Op::Load(1, 1),
          Op::AssertEq(vec![0], vec![2], None),
        ],
        ctrl: Ctrl::Return(0, vec![]),
      },
      layout: FunctionLayout {
        input_size: 1,
        selectors: 1,
        auxiliaries: 3,
        lookups: 3,
      },
      entry: true,
      constrained: true,
    };
    with_singleton_circuits(vec![f, h], vec![1])
  }

  #[test]
  fn deferred_call_is_answered_by_another_record() {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(deferral_toplevel(), cp, fp);
    let seven = G::from_u64(7);
    // Record 0 runs the claimed entry and owns nothing of `h`: its call is
    // pushed by `f`'s row and answered nowhere in the record.
    let deferring = || {
      let mut io0 = empty_io_buffer();
      let mut worker0 = QueryRecord::with_pointer_base(system.toplevel(), 0);
      worker0.ownership =
        Some(Ownership { callee: 1, owned: rustc_hash::FxHashSet::default() });
      let output = system
        .toplevel()
        .execute_in(0, vec![seven], &mut io0, &mut worker0)
        .expect("entry executes");
      (worker0, io0, output)
    };
    let (worker0, io0, output) = deferring();
    assert_eq!(worker0.deferred.get(&vec![seven]), Some(&1));
    let deferred = worker0.function_queries[1]
      .get_index_of(&[seven])
      .expect("the deferred call has an entry");
    assert_eq!(worker0.function_queries[1].mult_at(deferred), G::ZERO);
    assert!(worker0.memory_queries[&1].is_empty(), "nothing ran");

    // Record 1 owns `h`: runs it as an entry in its own pointer namespace,
    // drops the entry multiplicity no claim pulls, and absorbs record 0's
    // push.
    let owner = |deferred: &FxHashMap<Vec<G>, u64>, absorb: bool| {
      let mut io1 = empty_io_buffer();
      let mut worker1 =
        QueryRecord::with_pointer_base(system.toplevel(), pointer_stride(2));
      system
        .toplevel()
        .execute_in(1, vec![seven], &mut io1, &mut worker1)
        .expect("owner executes");
      let i = worker1.function_queries[1].get_index_of(&[seven]).unwrap();
      *worker1.function_queries[1].get_index_mut(i).unwrap().1 -= G::ONE;
      if absorb {
        worker1.absorb_deferred(1, deferred).expect("absorbed");
      }
      (worker1, io1)
    };
    let (worker1, io1) = owner(&worker0.deferred, true);
    let (claim, proof) = system
      .prove_records(
        0,
        &[seven],
        &output,
        &[(worker0, &io0), (worker1, &io1)],
        None,
      )
      .expect("two records plan within an unbounded budget");
    assert_eq!(proof.proofs.len(), 2);
    assert_eq!(proof.preamble.messages.len(), 2, "one interval, the owner's");
    system.verify(&claim, &proof).expect("two records prove one claim");

    // Unabsorbed, the owner's row pulls nothing and record 0's push hangs.
    let (worker0, io0, output) = deferring();
    let (worker1, io1) = owner(&worker0.deferred, false);
    let (claim, proof) = system
      .prove_records(
        0,
        &[seven],
        &output,
        &[(worker0, &io0), (worker1, &io1)],
        None,
      )
      .expect("two records plan within an unbounded budget");
    assert!(matches!(
      system.verify(&claim, &proof),
      Err(AiurVerificationError::Stark(VerificationError::UnbalancedBatch))
    ));
  }

  /// A record regenerated by re-execution proves exactly as a resident one:
  /// the supplier executes the owner afresh each time the batch asks for
  /// it (once per round), absorbing the deferred call each time, and the
  /// batch verifies — its round-two headers reproduce round one's.
  #[test]
  fn regenerated_record_proves_in_the_batch() {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(deferral_toplevel(), cp, fp);
    let seven = G::from_u64(7);
    let mut io0 = empty_io_buffer();
    let mut worker0 = QueryRecord::with_pointer_base(system.toplevel(), 0);
    worker0.ownership =
      Some(Ownership { callee: 1, owned: rustc_hash::FxHashSet::default() });
    let output = system
      .toplevel()
      .execute_in(0, vec![seven], &mut io0, &mut worker0)
      .expect("entry executes");
    let deferred = worker0.deferred.clone();
    let executions = std::cell::Cell::new(0usize);
    let owner = || {
      executions.set(executions.get() + 1);
      let mut io1 = empty_io_buffer();
      let mut worker1 =
        QueryRecord::with_pointer_base(system.toplevel(), pointer_stride(2));
      system
        .toplevel()
        .execute_in(1, vec![seven], &mut io1, &mut worker1)
        .expect("owner executes");
      let i = worker1.function_queries[1].get_index_of(&[seven]).unwrap();
      *worker1.function_queries[1].get_index_mut(i).unwrap().1 -= G::ONE;
      worker1.absorb_deferred(1, &deferred).expect("absorbed");
      Supplied::Owned(Box::new(worker1), Box::new(io1))
    };
    let (claim, proof) = system
      .prove_record_supplier(
        0,
        &[seven],
        || output.clone(),
        2,
        |r| {
          Ok(if r == 0 { Supplied::Borrowed(&worker0, &io0) } else { owner() })
        },
        None,
      )
      .expect("two records plan within an unbounded budget");
    assert_eq!(executions.get(), 2, "the owner ran once per round");
    system
      .verify(&claim, &proof)
      .expect("a regenerated record proves the claim");
  }

  #[test]
  fn nonzero_pointer_base_proves_and_closes_its_interval() {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(call_and_memory_toplevel(), cp, fp);
    let input = vec![G::from_u64(3), G::from_u64(5)];
    let mut io_buffer = empty_io_buffer();
    let (record, output) = system
      .toplevel()
      .execute_with_pointer_base(
        0,
        input.clone(),
        &mut io_buffer,
        pointer_stride(2),
      )
      .expect("execution succeeds");
    let plan = system.single_shard_plan(&record);
    assert_eq!(plan.memory_totals, vec![(1, pointer_stride(2), 1)]);
    let (claim, proof) = system.prove_from_execution_planned(
      0,
      &input,
      &io_buffer,
      record,
      &output,
      &plan,
      Retention::Retain,
    );
    system.verify(&claim, &proof).expect("shifted pointer namespace verifies");
  }

  #[test]
  fn closure_interval_policy() {
    let (system, input, record, output, io_buffer) = executed_call_and_memory();
    let plan = two_shard_plan([0..1, 0..0]);
    let (claim, proof) = system.prove_from_execution_planned(
      0,
      &input,
      &io_buffer,
      record,
      &output,
      &plan,
      Retention::Retain,
    );
    let pair = |width: u64, start: u64, end: u64| {
      let w = G::from_u64(width);
      [
        multi_stark::batch::BatchMessage::pull(
          Memory::memseg_args(w, G::from_u64(start)).to_vec(),
        ),
        multi_stark::batch::BatchMessage::push(
          Memory::memseg_args(w, G::from_u64(end)).to_vec(),
        ),
      ]
    };
    let with =
      |extra: Vec<[multi_stark::batch::BatchMessage<AiurConfig>; 2]>| {
        let mut preamble = proof.preamble.clone();
        for [pull, push] in extra {
          preamble.messages.push(pull);
          preamble.messages.push(push);
        }
        system.check_batch_policy(&claim, &preamble)
      };
    // The proof closes width 1 over `[0, 1)`. A later disjoint interval of
    // the same width, an empty one, and a wider width are all canonical.
    assert!(with(vec![pair(1, 1, 5)]).is_ok());
    assert!(with(vec![pair(1, 1, 1)]).is_ok());
    assert!(with(vec![pair(1, 7, 9), pair(2, 0, 3)]).is_ok());
    // Overlap, reversed order, an interval ending before it starts, and a
    // width out of order are not.
    assert!(with(vec![pair(1, 0, 2)]).is_err());
    assert!(with(vec![pair(1, 5, 9), pair(1, 2, 4)]).is_err());
    assert!(with(vec![pair(1, 9, 8)]).is_err());
    assert!(with(vec![pair(2, 0, 3), pair(1, 7, 9)]).is_err());
  }

  #[test]
  fn rejects_noncanonical_messages_and_extra_claims() {
    let (system, input, record, output, io_buffer) = executed_call_and_memory();
    let plan = two_shard_plan([0..1, 0..0]);
    let (claim, proof) = system.prove_from_execution_planned(
      0,
      &input,
      &io_buffer,
      record,
      &output,
      &plan,
      Retention::Retain,
    );

    let mut extra_message = proof.clone();
    extra_message.preamble.messages.push(
      multi_stark::batch::BatchMessage::push(vec![G::ZERO, G::ONE, G::TWO]),
    );
    assert!(matches!(
      system.verify(&claim, &extra_message),
      Err(AiurVerificationError::Policy(_))
    ));

    let mut swapped_polarity = proof.clone();
    swapped_polarity.preamble.messages.swap(0, 1);
    assert!(matches!(
      system.verify(&claim, &swapped_polarity),
      Err(AiurVerificationError::Policy(_))
    ));

    let mut second_claim = proof.clone();
    second_claim.preamble.headers[1].claims.push(claim.clone());
    assert!(matches!(
      system.verify(&claim, &second_claim),
      Err(AiurVerificationError::Policy(_))
    ));

    let mut no_claim = proof;
    no_claim.preamble.headers[0].claims.clear();
    assert!(matches!(
      system.verify(&claim, &no_claim),
      Err(AiurVerificationError::Policy(_))
    ));
  }
  /// A witness whose only real work is one row of `f` with its selector OFF:
  /// no constraint of `f` applies to the row, yet it still pulls a return
  /// message for the entry claim. `g` and the memory table carry no rows, so
  /// the only message in the batch is that forged return, matched by the
  /// verifier's claim.
  fn forged_entry_witness(
    system: &AiurSystem,
    io_buffer: &IOBuffer,
    output: G,
  ) -> (Vec<G>, SystemWitness<G>) {
    let record = QueryRecord::new(system.toplevel());
    let plan = ShardPlan {
      shards: vec![ShardRows { rows: vec![0..0; 5] }],
      memory_totals: vec![],
    };
    let index = system.row_index(&record, &plan);
    let mut witness =
      system.shard_witness(&record, io_buffer, &plan, &index, 0);

    let shape = &system.circuit_shapes()[F];
    let input = [G::from_u64(3), G::from_u64(5)];
    let mut claim = vec![function_channel(), G::from_usize(F)];
    claim.extend(input);
    claim.push(output);

    // `f`'s columns: inputs (2), selector (1), auxiliaries (5): multiplicity,
    // call output, store pointer, loaded value, product. The selector stays
    // zero; the multiplicity and the returned product are set freely.
    let mut row = vec![G::ZERO; shape.main_width];
    row[0] = input[0];
    row[1] = input[1];
    row[3] = G::ONE;
    row[7] = output;
    witness.traces[F] = RowMajorMatrix::new(row, shape.main_width);
    let mut builder = LookupValues::builder(1, &system.slot_arg_widths(F));
    builder.rows_mut()[0].pull(0, G::ONE, &claim);
    witness.lookups[F] = builder.finish();
    (claim, witness)
  }

  #[test]
  fn padding_row_cannot_pull_a_return_message() {
    let (cp, fp) = test_parameters();
    let system = AiurSystem::build(call_and_memory_toplevel(), cp, fp);
    let io_buffer = empty_io_buffer();
    let (claim, witness) =
      forged_entry_witness(&system, &io_buffer, G::from_u64(999));
    let shards = vec![ShardInput { claims: vec![claim.clone()], witness }];
    let proof = system.system.prove_batch(&system.key, shards, vec![]);
    assert!(system.verify(&claim, &proof).is_err(), "forged claim verified");
  }

  // The CUDA backend derives lookup messages from the committed trace
  // through the constraint graph and never reads the forged host lookup
  // witness this test plants, so on that backend the proof is of the trace
  // alone (whose padding rows are gated) and verifies.
  #[cfg(not(feature = "cuda"))]
  #[test]
  fn padding_memory_rows_cannot_carry_multiplicities() {
    let (system, input, record, output, io_buffer) = executed_call_and_memory();
    let plan = system.single_shard_plan(&record);
    let index = system.row_index(&record, &plan);
    let mut witness =
      system.shard_witness(&record, &io_buffer, &plan, &index, 0);

    // The honest memory table has one row; pad it to four, and let the
    // padding rows pull the all-zero message with multiplicities that
    // cancel among themselves (`1 + 1 - 2`), so the batch stays balanced.
    let width = system.circuit_shapes()[MEM].main_width;
    let real = witness.traces[MEM].values[..width].to_vec();
    let mut rows = vec![G::ZERO; 4 * width];
    rows[..width].copy_from_slice(&real);
    for (i, m) in [G::ONE, G::ONE, -G::TWO].into_iter().enumerate() {
      rows[(i + 1) * width] = m;
    }
    witness.traces[MEM] = RowMajorMatrix::new(rows, width);

    let slot_arg_widths = system.slot_arg_widths(MEM);
    let mut builder = LookupValues::builder(4, &slot_arg_widths);
    let mut writers = builder.rows_mut();
    let size = G::ONE;
    writers[0].pull(
      0,
      real[0],
      &Memory::lookup_args(size, real[2], &real[3..]),
    );
    writers[0].push(1, G::ONE, &Memory::memseg_args(size, real[2]));
    writers[0].pull(2, G::ONE, &Memory::memseg_args(size, real[2] + G::ONE));
    let zero = vec![G::ZERO; slot_arg_widths[0]];
    for (i, m) in [G::ONE, G::ONE, -G::TWO].into_iter().enumerate() {
      writers[i + 1].pull(0, m, &zero);
    }
    drop(writers);
    witness.lookups[MEM] = builder.finish();

    let mut claim = vec![function_channel(), G::ZERO];
    claim.extend(&input);
    claim.extend(&output);
    let shards = vec![ShardInput { claims: vec![claim.clone()], witness }];
    let messages = AiurSystem::boundary_messages(&plan);
    let proof = system.system.prove_batch(&system.key, shards, messages);
    assert!(
      system.verify(&claim, &proof).is_err(),
      "padding rows carried multiplicities"
    );
  }

  #[test]
  fn plan_shards_within_budget_bounds_every_shard() {
    let (system, _input, record, _output, _io_buffer) =
      executed_call_and_memory();
    let record_bytes = crate::execute::record_retained_bytes(&record);
    let single = system.single_shard_plan(&record);
    let single_peak = system.shard_peak_bytes(&single, 0, record_bytes);

    // Enough for the whole execution: the single-shard plan, unchanged.
    let (plan, peak) = system
      .plan_shards_within(&record, single_peak)
      .expect("the single shard fits its own peak");
    assert_eq!(plan.num_shards(), 1);
    assert_eq!(peak, single_peak);

    // Just below it: a batch whose every shard is projected to fit.
    let (plan, peak) = system
      .plan_shards_within(&record, single_peak - 1)
      .expect("a smaller budget still admits a plan");
    assert!(plan.num_shards() > 1);
    assert!(peak < single_peak);
    for shard in 0..plan.num_shards() {
      assert!(system.shard_peak_bytes(&plan, shard, record_bytes) <= peak);
    }
    for ci in 0..5 {
      let covered: usize = plan.shards.iter().map(|s| s.rows[ci].len()).sum();
      assert_eq!(covered, single.shards[0].rows[ci].len(), "circuit {ci}");
    }

    // Below the record plus the byte tables nothing can fit.
    assert!(system.plan_shards_within(&record, record_bytes).is_err());
  }

  #[test]
  fn sharded_proofs_are_reproducible() {
    let plan = two_shard_plan([0..0, 0..1]);
    // Execution is deterministic, so each prove starts from an equal record.
    let prove = |retention| {
      let (system, input, record, output, io_buffer) =
        executed_call_and_memory();
      system
        .prove_from_execution_planned(
          0, &input, &io_buffer, record, &output, &plan, retention,
        )
        .1
        .to_bytes()
        .expect("serialize")
    };
    let first = prove(Retention::Regenerate);
    let second = prove(Retention::Regenerate);
    let retained = prove(Retention::Retain);
    assert_eq!(first, second, "two regenerating proves differ");
    assert_eq!(first, retained, "retain and regenerate differ");
  }
}
