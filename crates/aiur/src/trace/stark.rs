//! Experimental multi-stark adapter for the certified circuit export.
//!
//! The verifier's program, artifact and fixed tables must come from the trusted
//! compilation, not from the proof supplier. This Rust adapter and multi-stark
//! are outside the Lean proof. In particular, the memoized semantics' acyclicity
//! hypothesis is not discharged by a lookup argument.
use super::{Polynomial, Trace, TracePlan};
use crate::{
  Execution,
  field::{FieldBackend, NativeField, PrimeField},
};
use multi_stark::{
  expr::Expr,
  lookup::{Lookup, logup_constraint_count, logup_max_degree, stage2_width},
  p3_field::{PrimeCharacteristicRing, PrimeField64},
  p3_matrix::{Matrix, dense::RowMajorMatrix},
  system::{CircuitInputs, ProverKey, System, SystemWitness},
  types::{CommitmentParameters, FriParameters, GoldilocksBlake3Config, Val},
};
#[cfg(feature = "parallel")]
use rayon::prelude::*;
use rustc_hash::FxHashMap;
use serde::Serialize;

mod batch;
mod grouping;
pub mod planning;
#[cfg(feature = "trace-profile")]
mod profile;
mod rom;
mod tables;
#[cfg(test)]
mod tests;
mod witness;
pub use batch::{StreamPlan, VerifyingKey};

/// Conversion at this concrete proving adapter only. The native configuration
/// writes its existing field values directly into multi-stark's matrices.
pub trait WitnessField: FieldBackend {
  fn into_stark(value: Self::Element) -> Val;
}
impl WitnessField for PrimeField {
  fn into_stark(value: u64) -> Val {
    Val::from_u64(value)
  }
}
impl WitnessField for NativeField<Val> {
  #[inline]
  fn into_stark(value: Val) -> Val {
    value
  }
}

pub type Proof = multi_stark::prover::Proof<GoldilocksBlake3Config>;
pub type BatchProof = multi_stark::batch::BatchProof<GoldilocksBlake3Config>;

// Separate message namespaces; callable/type IDs fix the shape within each.
const CALL: u64 = 1;
const ROM: u64 = 2;
const MEMSEG: u64 = 16;

/// CPU FRI configuration. Root Merkle caps also cover height-one circuits.
/// These are explicit protocol parameters, not a claimed security-bit estimate.
#[derive(Clone, Copy, Debug, Serialize)]
pub struct Parameters {
  pub log_blowup: usize,
  pub num_queries: usize,
}
impl Default for Parameters {
  fn default() -> Self {
    Self { log_blowup: 1, num_queries: 64 }
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
  plan: &'p TracePlan<'a, B>,
  system: System<GoldilocksBlake3Config>,
  key: ProverKey<GoldilocksBlake3Config>,
  names: Vec<String>,
  tables: Vec<tables::FixedTable>,
  rom: rom::Rom,
  lookup_plans: Vec<witness::LookupPlan>,
  members: Vec<Vec<usize>>,
  placements: Vec<grouping::Placement>,
  parameters: Parameters,
  segmented_memory: bool,
  gpu_lookup_only: bool,
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

impl<'p, 'a, B: WitnessField> Backend<'p, 'a, B> {
  pub fn new(
    plan: &'p TracePlan<'a, B>,
    parameters: Parameters,
  ) -> Result<Self, String> {
    Self::with_memory_policy(plan, parameters, false)
  }

  /// Batch proofs close contiguous memory ranges through authenticated
  /// boundary messages. A standalone proof uses the original first-row rule.
  pub fn for_batch(
    plan: &'p TracePlan<'a, B>,
    parameters: Parameters,
  ) -> Result<Self, String> {
    Self::with_memory_policy(plan, parameters, true)
  }

  /// Reconstruct the trusted batch system for verification or key export.
  /// Prover-only lookup settings must not affect these operations. Use the CPU
  /// host binary when verification must not initialize the CUDA backend.
  pub fn for_batch_verification(
    plan: &'p TracePlan<'a, B>,
    parameters: Parameters,
  ) -> Result<Self, String> {
    Self::build_with_lookup_policy(plan, parameters, true, None, false)
  }

  /// Explicit CUDA placement. CPU builds reject a requested device instead of
  /// silently running a different backend. Device placement does not change keys.
  pub fn for_batch_on_device(
    plan: &'p TracePlan<'a, B>,
    parameters: Parameters,
    device: Option<i32>,
  ) -> Result<Self, String> {
    Self::build(plan, parameters, true, device)
  }

  fn with_memory_policy(
    plan: &'p TracePlan<'a, B>,
    parameters: Parameters,
    segmented_memory: bool,
  ) -> Result<Self, String> {
    Self::build(plan, parameters, segmented_memory, None)
  }

  fn build(
    plan: &'p TracePlan<'a, B>,
    parameters: Parameters,
    segmented_memory: bool,
    device: Option<i32>,
  ) -> Result<Self, String> {
    let gpu_lookup_only =
      std::env::var("AIUR_TRACE_ONLY_LOOKUPS").as_deref() == Ok("1");
    Self::build_with_lookup_policy(
      plan,
      parameters,
      segmented_memory,
      device,
      gpu_lookup_only,
    )
  }

  fn build_with_lookup_policy(
    plan: &'p TracePlan<'a, B>,
    parameters: Parameters,
    segmented_memory: bool,
    device: Option<i32>,
    gpu_lookup_only: bool,
  ) -> Result<Self, String> {
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
    if plan.program.field.modulus() != Val::ORDER_U64 {
      return Err("multi-stark adapter requires the Goldilocks field".into());
    }
    if !(1..=4).contains(&parameters.log_blowup) || parameters.num_queries == 0
    {
      return Err(
        "expected log_blowup in 1..=4 and positive num_queries".into(),
      );
    }
    let rom = rom::Rom::new(plan);
    let mut inputs = vec![];
    let mut names = vec![];
    let placements = grouping::build(plan, &rom, &mut inputs, &mut names)?;
    let function_circuits = inputs.len();
    let tables = tables::fixed_tables(
      plan,
      &mut inputs,
      &mut names,
      parameters.log_blowup,
    )?;
    rom.append_circuits(&mut inputs, &mut names, segmented_memory)?;
    // Fail with an error before System::new's degree assertion. Grouping
    // is tuned below using the backend's compiled (constant-folded) degrees.
    let max_degree = (1 << parameters.log_blowup) + 1;
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
      if user_degree.max(lookup_degree) > max_degree {
        return Err(format!(
          "{name}: increase log_blowup for constraint degree {}",
          user_degree.max(lookup_degree)
        ));
      }
    }
    let config = GoldilocksBlake3Config::with_device(
      CommitmentParameters { log_blowup: parameters.log_blowup, cap_height: 0 },
      FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: parameters.num_queries,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
      },
      device,
    );
    let (mut system, key) = System::new(config, inputs);
    // Group messages only if the existing quotient degree suffices. This
    // reduces stage 2 without making its FFTs or the quotient FFT larger.
    for circuit in &mut system.circuits {
      let quotient = circuit.quotient_degree();
      for group in (2..=multi_stark::lookup::MAX_LOOKUP_GROUP
        .min(circuit.num_lookups))
        .rev()
      {
        let max_degree = circuit
          .graph
          .max_constraint_degree
          .max(logup_max_degree(&circuit.graph, group))
          as usize;
        if (max_degree.max(2) - 1).next_power_of_two() <= quotient {
          circuit.lookup_group_size = group;
          circuit.stage_2_width = stage2_width(circuit.num_lookups, group, 2);
          circuit.constraint_count = circuit.graph.zeros.len()
            + logup_constraint_count(circuit.num_lookups, group, 2);
          circuit.max_constraint_degree = max_degree;
          break;
        }
      }
    }
    let lookup_plans = system
      .circuits
      .iter()
      .map(|circuit| witness::LookupPlan::compile(&circuit.graph))
      .collect::<Result<_, _>>()?;
    let mut members = vec![vec![]; function_circuits];
    for (function, &chip) in plan.members.iter().enumerate() {
      members[placements[chip].circuit].push(function);
    }
    Ok(Self {
      plan,
      system,
      key,
      names,
      tables,
      rom,
      lookup_plans,
      members,
      placements,
      parameters,
      segmented_memory,
      gpu_lookup_only,
    })
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

  pub fn claim(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
  ) -> Result<Vec<Val>, String> {
    let id = self.plan.program.entry(entry)?.function;
    self.plan.program.inputs[id].validate(args, self.plan.program.field)?;
    self.plan.program.outputs[id].validate(output, self.plan.program.field)?;
    let chip = &self.plan.artifact.chips[self.plan.members[id]];
    Ok(
      [CALL, self.plan.callables[&chip.name] as u64]
        .into_iter()
        .map(Val::from_u64)
        .chain(args.iter().copied().map(B::into_stark))
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
    self.plan.validate_record(record)?;
    if trace.matrices.len() != self.plan.artifact.chips.len() {
      return Err("trace matrix count mismatch".into());
    }
    let table_counts = self.auxiliary_counts(record)?;
    let traces = self.convert_traces(record, trace, &table_counts)?;
    let (active, degrees) = self.trace_shape(&traces)?;
    self.check_shape(&active, &degrees)?;
    Ok(self.witness_from_main(traces))
  }

  /// CUDA's graph evaluator derives lookup messages from committed rows.
  /// Shape-only buffers deliberately fail closed if a CPU fallback tries to
  /// consume them. Full host buffers remain the default for fallback support.
  fn witness_from_main(
    &self,
    traces: Vec<RowMajorMatrix<Val>>,
  ) -> SystemWitness<Val> {
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
      SystemWitness::from_stage_1(traces, &self.system)
    }
  }

  fn auxiliary_counts(
    &self,
    record: &Execution<B>,
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
    if record.memory.iter().any(|entry| entry.multiplicity >= Val::ORDER_U64) {
      return Err("ROM count reaches field characteristic".into());
    }
    Ok(table_counts)
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
      traces.push(self.rom.witness(record, i)?);
    }
    Ok(traces)
  }

  fn trace_shape(
    &self,
    traces: &[RowMajorMatrix<Val>],
  ) -> Result<(Vec<bool>, Vec<u8>), String> {
    if traces.len() != self.system.circuits.len() {
      return Err("wrong circuit count".into());
    }
    let mut active = vec![];
    let mut degrees = vec![];
    for (trace, circuit) in traces.iter().zip(&self.system.circuits) {
      if trace.width != circuit.main_width
        || !trace.values.len().is_multiple_of(trace.width)
        || (trace.height() != 0 && !trace.height().is_power_of_two())
      {
        return Err("invalid main trace shape".into());
      }
      active.push(trace.height() != 0);
      if trace.height() != 0 {
        degrees.push(trace.height().ilog2() as u8);
      }
    }
    Ok((active, degrees))
  }

  /// Match fixed domains and bound total unit lookup consumers below the
  /// characteristic. Root caps cover every active matrix, including height 1.
  fn check_shape(&self, active: &[bool], degrees: &[u8]) -> Result<(), String> {
    if active.len() != self.system.circuits.len() || !active.contains(&true) {
      return Err("invalid circuit activation".into());
    }
    let mut degrees = degrees.iter();
    let mut budget = 1u64; // one public root
    for (circuit, &on) in self.system.circuits.iter().zip(active) {
      if !on {
        if circuit.preprocessed_height != 0 {
          return Err("inactive fixed table".into());
        }
        continue;
      }
      let log = *degrees.next().ok_or("missing trace height")?;
      // Goldilocks has 2-adicity 32. Include the commitment blowup.
      if usize::from(log) + self.parameters.log_blowup > 32 {
        return Err("trace domain exceeds Goldilocks capacity".into());
      }
      let height = 1u64 << log;
      if circuit.preprocessed_height != 0
        && circuit.preprocessed_height as u64 != height
      {
        return Err("fixed table height mismatch".into());
      }
      budget = height
        .checked_mul(circuit.num_lookups as u64)
        .and_then(|n| budget.checked_add(n))
        .filter(|&n| n < Val::ORDER_U64)
        .ok_or("lookup count reaches field characteristic")?;
    }
    if degrees.next().is_some() {
      return Err("extra trace heights".into());
    }
    Ok(())
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

  /// Verify using trusted compilation and the public call alone. No execution
  /// record, hints, witness matrices or prover-supplied table data are read.
  pub fn verify(
    &self,
    entry: &str,
    args: &[B::Element],
    output: &[B::Element],
    proof: &Proof,
  ) -> Result<(), String> {
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
