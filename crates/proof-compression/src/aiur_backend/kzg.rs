//! KZG proving for the final circuits exported by the Aiur compiler.
//!
//! The checked program, trace artifact and fixed tables are trusted inputs.
//! Only witness population depends on an execution record. Verification binds
//! the public call to those compiler circuits using the existing KZG protocol.
//! This host adapter is outside the Lean compiler's proof boundary.

use super::{AiurCurve, AiurField, Bn254};
use crate::kzg::{CurveScalar, KzgConfig, KzgCurve};
use aiur::{
  Execution, FieldWord,
  trace::{Placement, Trace, TracePlan},
};
use multi_stark::{
  config::ProofConfig,
  lookup::{LookupValues, logup_max_degree},
  system::{CircuitInputs, ProverKey, System, SystemWitness, extension_params},
};
use p3_matrix::Matrix;

mod circuits;
mod verifier;
mod witness;

pub use verifier::VerifyingKey;

pub type Proof<C = crate::kzg::Bn254> =
  multi_stark::prover::Proof<KzgConfig<C>>;

/// Conservative row cap shared by the Aiur adapters. The compiler's depth
/// gaps are below `2^24`; `2^39 * 2^24` is below both the BN254 and BLS12-381
/// scalar moduli, so a memo cycle cannot wrap its strictly decreasing depth
/// around the field.
pub const MAX_TOTAL_ROWS: u64 = 1 << 39;

/// Lower every compiler group, singleton chip, fixed map and ROM width to
/// the KZG circuit interface. Fixed columns come from the checked program.
pub fn circuit_inputs<F: AiurField>(
  plan: &TracePlan<'_, F>,
) -> Result<Vec<CircuitInputs<CurveScalar<F::Curve>>>, String> {
  Ok(circuits::build(plan)?.inputs)
}

/// [`circuit_inputs`] under an explicit lookup quotient-degree budget instead
/// of `IX_AIUR_KZG_LOOKUP_QUOTIENT_BUDGET`; `None` keeps every circuit's
/// quotient degree at its group-size-one value.
pub fn circuit_inputs_with_budget<F: AiurField>(
  plan: &TracePlan<'_, F>,
  lookup_quotient_budget: Option<usize>,
) -> Result<Vec<CircuitInputs<CurveScalar<F::Curve>>>, String> {
  Ok(circuits::build_with(plan, lookup_quotient_budget)?.inputs)
}

/// The lookup group size the compiler lowering selects for `input` under
/// `lookup_quotient_budget` (see [`circuit_inputs_with_budget`]), for
/// circuits built outside that lowering.
pub fn lookup_group_size<C: KzgCurve>(
  input: &CircuitInputs<CurveScalar<C>>,
  lookup_quotient_budget: Option<usize>,
) -> Result<usize, String> {
  if lookup_quotient_budget.is_some_and(|budget| !budget.is_power_of_two()) {
    return Err("lookup quotient budget must be a power of two".into());
  }
  let graph = input
    .compile_graph(&extension_params::<KzgConfig<C>>())
    .map_err(|error| format!("invalid circuit: {error:?}"))?;
  circuits::lookup_group_size(&graph, lookup_quotient_budget)
}

pub struct Backend<'p, 'a, F: AiurField = Bn254> {
  plan: &'p TracePlan<'a, F>,
  system: System<KzgConfig<F::Curve>>,
  key: ProverKey<KzgConfig<F::Curve>>,
  names: Vec<String>,
  placements: Vec<Placement<FieldWord>>,
  function_circuits: usize,
  tables: Vec<circuits::FixedTable>,
  memory_widths: Vec<usize>,
}

impl<'p, 'a, F: AiurField> Backend<'p, 'a, F> {
  /// The configuration must carry trusted proving powers. Production callers
  /// authenticate their Ignition or Filecoin prefix before constructing
  /// `KzgConfig`.
  pub fn new(
    plan: &'p TracePlan<'a, F>,
    config: KzgConfig<F::Curve>,
  ) -> Result<Self, String> {
    let lowered = circuits::build(plan)?;
    let params = extension_params::<KzgConfig<F::Curve>>();
    for (input, name) in lowered.inputs.iter().zip(&lowered.names) {
      let graph = input.compile_graph(&params).map_err(|error| {
        format!("{name}: invalid compiler circuit: {error:?}")
      })?;
      let degree = graph
        .max_constraint_degree
        .max(logup_max_degree(&graph, input.lookup_group_size))
        as usize;
      let quotient = (degree.max(2) - 1)
        .checked_next_power_of_two()
        .ok_or("quotient degree overflow")?;
      if quotient > config.max_quotient_degree() {
        return Err(format!(
          "{name}: quotient degree {quotient} exceeds KZG capacity {}",
          config.max_quotient_degree()
        ));
      }
      if let Some(fixed) = &input.preprocessed {
        let log = fixed
          .values
          .len()
          .checked_div(fixed.width)
          .filter(|height| height.is_power_of_two())
          .ok_or("invalid fixed table domain")?
          .ilog2() as usize;
        if log > config.max_log_degree()
          || log + quotient.ilog2() as usize > config.max_log_quotient_domain()
        {
          return Err(format!(
            "{name}: fixed table domain exceeds KZG capacity"
          ));
        }
      }
    }
    let (mut system, key) = System::new(config, lowered.inputs);
    verifier::bind_system(&mut system)?;
    Ok(Self {
      plan,
      system,
      key,
      names: lowered.names,
      placements: lowered.placements,
      function_circuits: lowered.function_circuits,
      tables: lowered.tables,
      memory_widths: lowered.memory_widths,
    })
  }

  pub fn system(&self) -> &System<KzgConfig<F::Curve>> {
    &self.system
  }

  pub fn circuit_names(&self) -> &[String] {
    &self.names
  }

  /// `[CALL, callable, inputs..., depth?, outputs...]`, with the compiler's
  /// typed layouts checked before the public lookup demand is constructed.
  pub fn claim(
    &self,
    entry: &str,
    args: &[CurveScalar<F::Curve>],
    output: &[CurveScalar<F::Curve>],
  ) -> Result<Vec<CurveScalar<F::Curve>>, String> {
    self.plan.public_claim(entry, args, output)
  }

  pub fn generate(
    &self,
    record: &Execution<F>,
    entry: &str,
    args: &[CurveScalar<F::Curve>],
  ) -> Result<SystemWitness<CurveScalar<F::Curve>>, String> {
    let (trace, timings) =
      self.plan.generate_profiled(record, entry, args, true, false)?;
    tracing::info!(
      validate_seconds = timings.validate_seconds,
      allocation_seconds = timings.bind_seconds,
      fill_seconds = timings.fill_seconds,
      "Aiur logical traces populated"
    );
    self.pack(record, &trace)
  }

  /// Validate the populated compiler rows and exact integer lookup balance
  /// before packing native scalar columns for the prover. The verifier never
  /// consumes this record or trusts these diagnostics.
  pub fn witness(
    &self,
    record: &Execution<F>,
    trace: &Trace<CurveScalar<F::Curve>>,
    entry: &str,
    args: &[CurveScalar<F::Curve>],
  ) -> Result<SystemWitness<CurveScalar<F::Curve>>, String> {
    self.plan.check(record, trace, entry, args)?;
    self.pack(record, trace)
  }

  fn pack(
    &self,
    record: &Execution<F>,
    trace: &Trace<CurveScalar<F::Curve>>,
  ) -> Result<SystemWitness<CurveScalar<F::Curve>>, String> {
    let started = std::time::Instant::now();
    let widths: Vec<_> = self.system.circuits[..self.function_circuits]
      .iter()
      .map(|circuit| circuit.main_width)
      .collect();
    let traces = witness::Packing {
      plan: self.plan,
      placements: &self.placements,
      function_widths: &widths,
      tables: &self.tables,
      memory_widths: &self.memory_widths,
    }
    .main_traces(record, trace)?;
    tracing::info!(
      seconds = started.elapsed().as_secs_f64(),
      "Aiur physical traces packed"
    );
    let (active, degrees) = self.trace_shape(&traces)?;
    self.check_shape(&active, &degrees)?;
    if !self.system.config.uses_streaming_lookups() {
      return Ok(SystemWitness::from_stage_1(traces, &self.system));
    }
    // Concrete lookup tuples can exceed the trace matrices by several times.
    // The prover rebuilds them from committed columns, including CPU fallbacks.
    let lookups = traces
      .iter()
      .zip(&self.system.circuits)
      .map(|(trace, circuit)| {
        let widths: Vec<_> = circuit
          .graph
          .lookups
          .iter()
          .map(|lookup| lookup.args.len())
          .collect();
        LookupValues::shape_only(trace.height(), &widths)
      })
      .collect();
    Ok(SystemWitness { traces, lookups })
  }

  /// A malformed witness can produce an invalid proof. Verification against
  /// the trusted compiler artifact and independently expected call is final.
  pub fn prove(
    &self,
    entry: &str,
    args: &[CurveScalar<F::Curve>],
    output: &[CurveScalar<F::Curve>],
    witness: SystemWitness<CurveScalar<F::Curve>>,
  ) -> Result<Proof<F::Curve>, String> {
    let claim = self.claim(entry, args, output)?;
    let (active, degrees) = self.trace_shape(&witness.traces)?;
    self.check_shape(&active, &degrees)?;
    if witness.lookups.len() != self.system.circuits.len() {
      return Err("wrong lookup witness count".into());
    }
    Ok(self.system.prove(&self.key, &claim, witness))
  }

  pub fn verify(
    &self,
    entry: &str,
    args: &[CurveScalar<F::Curve>],
    output: &[CurveScalar<F::Curve>],
    proof: &Proof<F::Curve>,
  ) -> Result<(), String> {
    let claim = self.claim(entry, args, output)?;
    self.check_shape(&proof.active, &proof.log_degrees)?;
    self
      .system
      .verify(&claim, proof)
      .map_err(|error| format!("Aiur KZG verification failed: {error:?}"))
  }

  fn check_shape(&self, active: &[bool], degrees: &[u8]) -> Result<(), String> {
    check_shape(&self.system, active, degrees)
  }
}

/// Shared compiler lowering and witness packing, independent of the proof
/// protocol and its setup. Capacities belong to each consuming backend.
pub struct Compiler<'p, 'a, F: AiurField = Bn254> {
  plan: &'p TracePlan<'a, F>,
  lowered: circuits::Lowered<F::Curve>,
  function_widths: Vec<usize>,
}

impl<'p, 'a, F: AiurField> Compiler<'p, 'a, F> {
  pub fn new(plan: &'p TracePlan<'a, F>) -> Result<Self, String> {
    Ok(Self::from_lowered(plan, circuits::build(plan)?))
  }

  pub fn with_lookup_budget(
    plan: &'p TracePlan<'a, F>,
    lookup_quotient_budget: Option<usize>,
  ) -> Result<Self, String> {
    Ok(Self::from_lowered(
      plan,
      circuits::build_with(plan, lookup_quotient_budget)?,
    ))
  }

  fn from_lowered(
    plan: &'p TracePlan<'a, F>,
    lowered: circuits::Lowered<F::Curve>,
  ) -> Self {
    let function_widths = lowered.inputs[..lowered.function_circuits]
      .iter()
      .map(|input| input.main_width)
      .collect();
    Self { plan, lowered, function_widths }
  }

  pub fn inputs(&self) -> &[CircuitInputs<CurveScalar<F::Curve>>] {
    &self.lowered.inputs
  }
  pub fn names(&self) -> &[String] {
    &self.lowered.names
  }

  /// Function circuits receive their first message and send the rest.
  /// Fixed maps and ROM circuits only receive lookup demands.
  pub fn lookup_pulls(
    &self,
    circuit: usize,
  ) -> Option<impl ExactSizeIterator<Item = bool>> {
    let count = self.lowered.inputs.get(circuit)?.lookups.len();
    let table = circuit >= self.lowered.function_circuits;
    Some((0..count).map(move |lookup| table || lookup == 0))
  }

  /// Exact padded main-trace heights in `inputs()`/`names()` order. This
  /// reads query and ROM counts without populating rows or lookup witnesses;
  /// it estimates storage for the record and does not validate its arithmetic.
  pub fn row_counts(
    &self,
    record: &Execution<F>,
  ) -> Result<Vec<usize>, String> {
    let mut heights = self.raw_row_counts(record)?;
    for height in &mut heights {
      if *height != 0 {
        *height =
          height.checked_next_power_of_two().ok_or("trace height overflow")?;
      }
    }
    Ok(heights)
  }

  /// Rows each circuit's execution fills, before power-of-two padding.
  /// Fixed tables report their full height.
  pub fn raw_row_counts(
    &self,
    record: &Execution<F>,
  ) -> Result<Vec<usize>, String> {
    let mut heights = vec![0usize; self.lowered.inputs.len()];
    for (function, &chip) in self.plan.function_chips().iter().enumerate() {
      let count = record
        .queries
        .callable_rows(function)
        .ok_or("missing function query table")?;
      if record.queries.fixed_counts(function).is_some() {
        return Err("function query table has fixed-map storage".into());
      }
      let circuit = self.lowered.placements[chip].circuit;
      heights[circuit] = heights[circuit]
        .checked_add(count)
        .ok_or("function row count overflow")?;
    }
    let program = self.plan.program().program();
    for (map, definition) in program.maps.iter().enumerate() {
      let counts = record
        .queries
        .fixed_counts(program.functions.len() + map)
        .ok_or("missing fixed-map counts")?;
      if counts.len() != program.tables[definition.input].rows.len() {
        return Err("fixed-map row count mismatch".into());
      }
    }
    for (table, definition) in self.lowered.tables.iter().enumerate() {
      heights[self.lowered.function_circuits + table] = definition.height;
    }
    let memory_start =
      self.lowered.function_circuits + self.lowered.tables.len();
    for (width, count) in record.memory.width_counts() {
      if count == 0 {
        continue;
      }
      let bucket =
        self.lowered.memory_widths.binary_search(&width).map_err(
          |_error| "recorded ROM width absent from compiler circuits",
        )?;
      heights[memory_start + bucket] = count;
    }
    Ok(heights)
  }

  /// Function circuits come first; tables and ROM circuits follow them.
  pub fn function_circuits(&self) -> usize {
    self.lowered.function_circuits
  }

  /// Per fixed map table circuit (in circuit order, after the function
  /// circuits): its fixed maps, one main count column each.
  pub fn map_tables(&self) -> Vec<Vec<usize>> {
    self.lowered.tables.iter().map(|t| t.maps.clone()).collect()
  }

  pub fn generate(
    &self,
    record: &Execution<F>,
    entry: &str,
    args: &[CurveScalar<F::Curve>],
  ) -> Result<
    Vec<p3_matrix::dense::RowMajorMatrix<CurveScalar<F::Curve>>>,
    String,
  > {
    let trace = self.plan.generate(record, entry, args, true)?;
    witness::Packing {
      plan: self.plan,
      placements: &self.lowered.placements,
      function_widths: &self.function_widths,
      tables: &self.lowered.tables,
      memory_widths: &self.lowered.memory_widths,
    }
    .main_traces(record, &trace)
  }
}

pub(crate) fn check_shape<C: ProofConfig>(
  system: &System<C>,
  active: &[bool],
  degrees: &[u8],
) -> Result<(), String> {
  if active.len() != system.circuits.len() || !active.contains(&true) {
    return Err("invalid circuit activation".into());
  }
  let mut degrees = degrees.iter();
  let mut rows = 0u64;
  let mut budget = 1u64;
  for (circuit, &on) in system.circuits.iter().zip(active) {
    if !on {
      if circuit.preprocessed_height != 0 {
        return Err("inactive fixed table".into());
      }
      continue;
    }
    let log = usize::from(*degrees.next().ok_or("missing trace height")?);
    if log > system.config.max_log_degree()
      || log + circuit.quotient_degree().ilog2() as usize
        > system.config.max_log_quotient_domain()
    {
      return Err("trace domain exceeds KZG capacity".into());
    }
    let height = 1u64
      .checked_shl(
        u32::try_from(log).map_err(|_error| "trace height overflow")?,
      )
      .ok_or("trace height overflow")?;
    if circuit.preprocessed_height != 0
      && u64::try_from(circuit.preprocessed_height).ok() != Some(height)
    {
      return Err("fixed table height mismatch".into());
    }
    rows = rows
      .checked_add(height)
      .filter(|&rows| rows <= MAX_TOTAL_ROWS)
      .ok_or("trace rows exceed the Aiur row bound (2^39)")?;
    // Every u64 integer is below the BN254 scalar characteristic. Requiring
    // this aggregate to fit u64 is a conservative no-wrap lookup bound.
    budget = height
      .checked_mul(
        u64::try_from(circuit.num_lookups.max(1))
          .map_err(|_error| "lookup count overflow")?,
      )
      .and_then(|count| budget.checked_add(count))
      .ok_or("lookup count overflow")?;
  }
  if degrees.next().is_some() {
    return Err("extra trace heights".into());
  }
  Ok(())
}
