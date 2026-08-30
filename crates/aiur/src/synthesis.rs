use multi_stark::{
  expr::Expr,
  lookup::Lookup,
  p3_field::PrimeCharacteristicRing,
  p3_matrix::dense::RowMajorMatrix,
  prover::Proof,
  system::{CircuitInputs, ProverKey, System, SystemWitness},
  types::{
    CommitmentParameters, FriParameters, GoldilocksBlake3Config, PcsError,
  },
  verifier::VerificationError,
};
use rayon::iter::{
  IndexedParallelIterator, IntoParallelIterator, ParallelIterator,
};

use crate::{
  G,
  bytecode::{FunIdx, Toplevel},
  execute::{ExecError, IOBuffer, QueryRecord},
  function_channel,
  gadgets::{AiurGadget, bytes1::Bytes1, bytes2::Bytes2},
  memory::Memory,
};

/// The concrete STARK configuration Aiur instantiates multi-stark with.
pub type AiurConfig = GoldilocksBlake3Config;
/// A proof under [`AiurConfig`].
pub type AiurProof = Proof<AiurConfig>;

/// The prover RAM model's phase breakdown; `peak` is the number the
/// budget gate compares (see [`AiurSystem::peak_prove_bytes`]).
pub struct PeakProveBytes {
  pub phase_witness: usize,
  pub phase_stage2: usize,
  pub phase_open: usize,
  pub preprocessed: usize,
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

fn calibrate_prover_rss(analytic_peak: usize) -> usize {
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

enum CircuitType {
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
/// even shares — `parts = 1` is the record's exact heights. The byte
/// gadgets keep their fixed heights: they are the same size in every
/// shard and are most of the peak model's floor, which dividing cannot
/// shrink.
fn raw_of(
  record: &QueryRecord,
  parts: usize,
) -> impl Fn(usize, &CircuitType) -> usize + '_ {
  move |_, ct| match ct {
    CircuitType::Function { idx } => {
      record.function_queries[*idx].len().div_ceil(parts)
    },
    CircuitType::Memory { width } => {
      record.memory_queries.get(width).map_or(0, |m| m.len().div_ceil(parts))
    },
    CircuitType::Bytes1 => 256,
    CircuitType::Bytes2 => 65536,
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

    // Constrained functions (ascending index).
    for i in 0..toplevel.functions.len() {
      if !toplevel.functions[i].constrained {
        continue;
      }
      let (constraints, lookups) = toplevel.build_constraints(i);
      // A branchless function's lookup arguments are sent raw (degree 1;
      // see `ConstraintState::gate`), so two lookups fit in one chained
      // accumulator step at degree 3 — within the degree the selector-gated
      // constraints already pay for. Branching functions keep k = 1: their
      // superposed arguments are degree 2, and grouping would push the
      // logUp constraints past the quotient budget.
      let group_size =
        if toplevel.functions[i].layout.selectors == 1 && lookups.len() >= 2 {
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
  fn circuit_types(&self) -> Vec<CircuitType> {
    let functions = (0..self.toplevel.functions.len()).filter_map(|idx| {
      self.toplevel.functions[idx]
        .constrained
        .then_some(CircuitType::Function { idx })
    });
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
  fn slot_arg_widths(&self, circuit_idx: usize) -> Vec<usize> {
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
      raw_of(record, 1),
      crate::execute::record_retained_bytes(record),
    )
  }

  fn peak_prove_bytes_by(
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
      let d = c.stage_2_width / (1 + c.num_lookups); // extension degree
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
        .peak_prove_bytes_by(raw_of(record, parts), record_bytes / parts)
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
    let _g = tracing::info_span!("aiur/witness").entered();
    let circuit_types = self.circuit_types();
    let witness_data = circuit_types
      .into_par_iter()
      .enumerate()
      .map(|(circuit_idx, circuit_type)| {
        let slot_arg_widths = self.slot_arg_widths(circuit_idx);
        match circuit_type {
          CircuitType::Function { idx } => self.toplevel.witness_data(
            idx,
            &query_record,
            io_buffer,
            &slot_arg_widths,
          ),
          CircuitType::Memory { width } => {
            Memory::witness_data(width, &query_record, &slot_arg_widths)
          },
          CircuitType::Bytes1 => {
            Bytes1.witness_data(&query_record, &slot_arg_widths)
          },
          CircuitType::Bytes2 => {
            Bytes2.witness_data(&query_record, &slot_arg_widths)
          },
        }
      })
      .collect::<Vec<_>>();
    drop(query_record); // Early drop to free memory.
    let (traces, lookups) = witness_data.into_iter().unzip();
    let witness = SystemWitness { traces, lookups };
    drop(_g);

    // Construct the claim.
    let mut claim = vec![function_channel(), G::from_usize(fun_idx)];
    claim.extend(input);
    claim.extend(output);

    // Finally prove.
    let proof = self.system.prove(&self.key, &claim, witness);
    (claim, proof)
  }

  #[tracing::instrument(level = "info", skip_all, name = "aiur/prove")]
  pub fn prove(
    &self,
    fun_idx: FunIdx,
    input: &[G],
    io_buffer: &mut IOBuffer,
  ) -> (Vec<G>, AiurProof) {
    #[cfg(feature = "texray")]
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
      fun_idx, input, io_buffer, executor, None, false,
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
  /// the LDE/commit/FRI phases that would actually exhaust the box: the
  /// record is dropped and [`GatedProve::Split`] carries the part count
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
  ) -> GatedProve
  where
    F: FnOnce(
      &Toplevel,
      FunIdx,
      Vec<G>,
      &mut IOBuffer,
    ) -> Result<(QueryRecord, Vec<G>), ExecError>,
  {
    #[cfg(feature = "texray")]
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

  #[inline]
  pub fn verify(
    &self,
    claim: &[G],
    proof: &AiurProof,
  ) -> Result<(), VerificationError<PcsError>> {
    self.system.verify(claim, proof)
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
    execute::IOBuffer,
  };
  use multi_stark::{
    p3_field::PrimeCharacteristicRing,
    types::{CommitmentParameters, FriParameters},
  };
  use rustc_hash::FxHashMap;

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
    Toplevel { functions: vec![function], memory_sizes: vec![] }
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
    Toplevel { functions: vec![function], memory_sizes: vec![] }
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

    // The terminal zkVM receives only the serialized verifier key, not the
    // prover-side `AiurSystem`. Exercise that exact path against a real proof
    // so codec round trips alone cannot mask a transcript/config mismatch.
    let vk_bytes = crate::vk_codec::aiur_system_to_bytes(&system)
      .expect("encode verifier key");
    let vk = crate::vk_codec::AiurVerifyingKey::from_bytes(&vk_bytes)
      .expect("decode verifier key");
    assert_eq!(vk.to_bytes(), vk_bytes, "verifier key is canonical");
    vk.verify(&claim, &proof).expect("decoded verifier key must verify");

    let mut tampered_claim = claim.clone();
    tampered_claim[2] += G::ONE;
    assert!(
      vk.verify(&tampered_claim, &proof).is_err(),
      "decoded verifier key must bind the outer claim"
    );
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

    Toplevel { functions: vec![f, g], memory_sizes: vec![1] }
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

    Toplevel { functions: vec![f, g, h], memory_sizes: vec![] }
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
}
