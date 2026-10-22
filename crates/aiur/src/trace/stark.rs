//! Experimental multi-stark adapter for the certified circuit export.
//!
//! The verifier's program, artifact and fixed tables must come from the trusted
//! compilation, not from the proof supplier. This Rust adapter and multi-stark
//! are outside the Lean proof. In particular, the memoized semantics' acyclicity
//! hypothesis is not discharged by a lookup argument.
use super::{Polynomial, Trace, TracePlan};
use crate::{
  Execution,
  bytecode::Type,
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
mod rom;
mod tables;
#[cfg(test)]
mod tests;
mod witness;
pub use batch::VerifyingKey;

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
  parameters: Parameters,
  segmented_memory: bool,
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

  fn with_memory_policy(
    plan: &'p TracePlan<'a, B>,
    parameters: Parameters,
    segmented_memory: bool,
  ) -> Result<Self, String> {
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
    for chip in &plan.artifact.chips {
      if chip.width >= u32::MAX as usize {
        return Err("too many circuit columns".into());
      }
      let mut args =
        vec![constant(CALL), constant(plan.callables[&chip.name] as u64)];
      args.extend(chip.inputs.iter().map(|&i| main_var(i)));
      args.extend(chip.output.iter().map(lower));
      let mut lookups = vec![Lookup::pull(main_var(chip.width), args)];
      for send in &chip.sends {
        let mut args =
          vec![constant(CALL), constant(plan.callables[&send.channel] as u64)];
        args.extend(send.args.iter().map(lower));
        args.extend(send.result.iter().map(|&i| main_var(i)));
        lookups.push(Lookup::push(lower(&send.enable), args));
      }
      for cell in &chip.memory {
        lookups.push(rom.access(cell)?);
      }
      inputs.push(CircuitInputs {
        main_width: chip.width + 1,
        constraints: chip
          .constraints
          .iter()
          .map(lower)
          .chain([
            // An inactive row cannot provide a claim, even if a prover
            // forges its count independently of the row generator.
            (constant(1) - main_var(chip.activation)) * main_var(chip.width),
          ])
          .collect(),
        lookups,
        ..Default::default()
      });
      names.push(chip.name.clone());
    }
    let tables = tables::fixed_tables(plan, &mut inputs, &mut names)?;
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
    let config = GoldilocksBlake3Config::new(
      CommitmentParameters { log_blowup: parameters.log_blowup, cap_height: 0 },
      FriParameters {
        log_final_poly_len: 0,
        max_log_arity: 1,
        num_queries: parameters.num_queries,
        commit_proof_of_work_bits: 0,
        query_proof_of_work_bits: 0,
      },
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
    let mut members = vec![vec![]; plan.artifact.chips.len()];
    for (function, &chip) in plan.members.iter().enumerate() {
      members[chip].push(function);
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
      parameters,
      segmented_memory,
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
    let (table_counts, memory_counts) = self.auxiliary_counts(record)?;
    let traces =
      self.convert_traces(record, trace, &table_counts, &memory_counts)?;
    let (active, degrees) = self.trace_shape(&traces)?;
    self.check_shape(&active, &degrees)?;
    Ok(SystemWitness::from_stage_1(traces, &self.system))
  }

  fn auxiliary_counts(
    &self,
    record: &Execution<B>,
  ) -> Result<(Vec<Vec<u64>>, Vec<u64>), String> {
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
    let memory_counts = record
      .memory
      .iter()
      .map(|entry| {
        (entry.multiplicity < Val::ORDER_U64)
          .then_some(entry.multiplicity)
          .ok_or("ROM count reaches field characteristic")
      })
      .collect::<Result<Vec<_>, _>>()?;
    Ok((table_counts, memory_counts))
  }

  fn convert_traces(
    &self,
    record: &Execution<B>,
    trace: &Trace<B::Element>,
    table_counts: &[Vec<u64>],
    memory_counts: &[u64],
  ) -> Result<Vec<RowMajorMatrix<Val>>, String> {
    let mut traces = Vec::with_capacity(self.system.circuits.len());
    for (chip, matrix) in self.plan.artifact.chips.iter().zip(&trace.matrices) {
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
      let width = chip.width + 1;
      let mut values = Vec::with_capacity(
        matrix.height.checked_mul(width).ok_or("trace size overflow")?,
      );
      for r in 0..matrix.height {
        let row = matrix.row(r);
        values.extend(row.iter().copied().map(B::into_stark));
        values.push(Val::from_u64(matrix.multiplicities[r]));
        if row[chip.activation] != self.plan.program.field.zero()
          && row[chip.activation] != self.plan.program.field.one()
        {
          return Err("non-boolean row activation".into());
        }
        if row[chip.activation] == self.plan.program.field.zero()
          && matrix.multiplicities[r] != 0
        {
          return Err("inactive row provides a claim".into());
        }
      }
      traces.push(RowMajorMatrix::new(values, width));
    }
    for table in &self.tables {
      traces.push(table.witness(table_counts));
    }
    let rows = self.rom.partition(record, memory_counts)?;
    for i in 0..self.rom.circuit_count() {
      traces.push(self.rom.witness(&rows, i)?);
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
